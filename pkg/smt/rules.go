package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
	"github.com/vhavlena/verirego/pkg/types"
)

// pathParamName is the synthetic parameter name used for the path argument
// (Seq OTypeD0) in every contains-rule predicate function.
const pathParamName = "__pathP__"

// ruleHeadName returns the base variable name for a rule.
// For most rules this is rule.Head.Name. For subscripted or dotted-path rules
// (e.g. reasons[key] contains msg, rule.a.b := v) rule.Head.Name is empty and
// the name must be read from the first element of rule.Head.Ref().
func ruleHeadName(rule *ast.Rule) ast.Var {
	if rule.Head.Name != "" {
		return rule.Head.Name
	}
	ref := rule.Head.Ref()
	if len(ref) > 0 {
		if v, ok := ref[0].Value.(ast.Var); ok {
			return v
		}
	}
	return rule.Head.Name
}

// containsRuleSmtName returns the SMT function name for a contains rule.
// All contains rules use the base variable name (ref[0]); the path elements
// are encoded as the first (Seq OTypeD0) parameter at call time, not in the name.
func containsRuleSmtName(rule *ast.Rule) string {
	return ruleHeadName(rule).String()
}

// ruleHeadValueSmt returns smt values for a rule variable and its corresponding value
//
// Returns:
//
//	*SmtValue: variable (or field-select expression for dotted-path rules)
//	*SmtValue: value
//	error
func (t *Translator) ruleHeadValueSmt(rule *ast.Rule, exprTrans *ExprTranslator) (*SmtValue, *SmtValue, error) {
	if rule == nil || rule.Head == nil {
		return nil, nil, fmt.Errorf("invalid rule: nil head")
	}
	// For contains rules the SMT name may encode a dotted path (e.g. rule_a_b).
	// Look it up via the compound name so the correct FunctionType is found.
	var ruleVar *SmtValue
	var err error
	if rule.Head.Key != nil && len(rule.Head.Args) == 0 {
		smtName := containsRuleSmtName(rule)
		ruleVar, err = NewSmtValueFromVar(ast.Var(smtName), exprTrans)
		if err != nil {
			return nil, nil, fmt.Errorf("failed to convert contains rule head: %w", err)
		}
		ruleVal := NewSmtValueFromBoolean(true).WrapToDepth(0)
		return ruleVar, ruleVal, nil
	}
	ruleVar, err = NewSmtValueFromVar(ruleHeadName(rule), exprTrans)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to convert rule head value: %w", err)
	}
	// dotted-path rule (e.g. rule.a.b := v or rule.status := v): navigate constant string
	// path elements so the returned head SmtValue is the field-select expression.
	if len(rule.Head.Ref()) > 1 && rule.Head.Key == nil && len(rule.Head.Args) == 0 {
		pathVal := ruleVar
		for _, term := range rule.Head.Ref()[1:] {
			str, ok := term.Value.(ast.String)
			if !ok {
				return nil, nil, fmt.Errorf("unsupported non-constant path element in dotted-path rule")
			}
			key := fmt.Sprintf("%q", string(str))
			pathVal = pathVal.SelectObj(key)
		}
		ruleValSmt, err := exprTrans.termToSmtValue(rule.Head.Value)
		if err != nil {
			return nil, nil, fmt.Errorf("failed to convert dotted-path rule head value: %w", err)
		}
		return pathVal, ruleValSmt, nil
	}
	ruleValSmt, err := exprTrans.termToSmtValue(rule.Head.Value)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to convert rule head value: %w", err)
	}
	return ruleVar, ruleValSmt, nil
}

// ruleToSmtCore translates a rule into SMT head/value pair. The getDefault callback
// returns the fallback SmtValue used when rule.Else is nil; it receives the rule's
// declared name and its inferred type depth.
func (t *Translator) ruleToSmtCore(
	rule *ast.Rule,
	getDefault func(name string, depth int) (*SmtValue, error),
) (*SmtValue, *SmtValue, error) {
	exprTrans := t.IntoExprTranslator()
	smtHead, smtVal, err := t.ruleHeadValueSmt(rule, exprTrans)
	if err != nil {
		return nil, nil, err
	}

	// Compute pre-defined parameters for body translation.
	// For contains rules: only pre-define the value key (not the path param or subscript vars).
	//   - pathParamName (__pathP__) never appears in the body → no need to pre-define.
	//   - subscript variables in Head.Ref()[1:] become let-bindings; they appear in the
	//     path constraint added after body translation.
	//   - the value key (Head.Key) is a function parameter → pre-define so assignments
	//     to it produce comparison constraints.
	// For parametric rules: pre-define all args (existing behaviour).
	args, err := t.getArgs(rule)
	if err != nil {
		return nil, nil, err
	}
	preDefined := make(map[string]bool, len(args))
	for _, arg := range args {
		if arg.typ.depth != seqArgDepth { // skip the Seq path parameter
			preDefined[arg.name] = true
		}
	}

	bodySmt, localVarDefs, err := exprTrans.bodyToSmtWithPredefined(&rule.Body, preDefined)
	if err != nil {
		return nil, nil, err
	}

	// For contains rules, add the path constraint so the function body discriminates
	// by path: (= __pathP__ path_literal_from_ref).
	if rule.Head.Key != nil && len(rule.Head.Args) == 0 {
		pathSmt, err := buildPathSmtValue(rule, exprTrans)
		if err != nil {
			return nil, nil, err
		}
		pathConstraint := RawProposition(fmt.Sprintf("(= %s %s)", pathParamName, pathSmt.String()))
		bodySmt = AndPtrs([]*SmtProposition{pathConstraint, bodySmt})
	}
	t.AddTransContext(exprTrans.GetTransContext())

	// For contains rules with dotted paths, use the compound SMT name (e.g. "rule_a_b")
	// so that GetDefaultValue finds the correct FunctionType entry.
	var name string
	if rule.Head.Key != nil && len(rule.Head.Args) == 0 {
		name = containsRuleSmtName(rule)
	} else {
		name = ruleHeadName(rule).String()
	}
	depth := 0
	if tp, ok := t.TypeTrans.TypeInfo.Types[name]; ok {
		depth = max(tp.TypeDepth(), 0)
	}
	// For dotted-path rules the default value is for the leaf field, not the base object.
	// Use the head value variable's type depth so OUndef is generated at the correct sort.
	defaultName := name
	if len(rule.Head.Ref()) > 1 && rule.Head.Key == nil && len(rule.Head.Args) == 0 && rule.Head.Value != nil {
		if v, ok := rule.Head.Value.Value.(ast.Var); ok {
			leafName := removeQuotes(v.String())
			if tp, ok := t.TypeTrans.TypeInfo.Types[leafName]; ok {
				depth = tp.TypeDepth()
				defaultName = leafName
			}
		}
	}

	var elseSmt *SmtValue
	if rule.Else != nil {
		_, elseSmt, err = t.ruleToSmtCore(rule.Else, getDefault)
		if err != nil {
			return nil, nil, err
		}
	} else {
		elseSmt, err = getDefault(defaultName, depth)
		if err != nil {
			return nil, nil, err
		}
	}

	smt := Ite(bodySmt, smtVal, elseSmt)
	for i := len(localVarDefs) - 1; i >= 0; i-- {
		smt = Let(localVarDefs[i], smt)
	}
	return smtHead, smt, nil
}

// ruleToSmtString returns smt values for a rule variable and for its assignment based on the rule.
// Falls back to the declared default value (or OUndef when none is set).
//
// Returns:
//
//	*SmtValue: variable
//	*SmtValue: assignment - value, which is conditional to the rule body
//	error
func (t *Translator) ruleToSmtString(rule *ast.Rule) (*SmtValue, *SmtValue, error) {
	return t.ruleToSmtCore(rule, func(name string, _ int) (*SmtValue, error) {
		return t.GetDefaultValue(name)
	})
}

func (t *Translator) getArgs(rule *ast.Rule) ([]Arg, error) {
	// For contains rules: rule(path: Seq OTypeD0, value: OTypeD0) -> Boolean.
	// The path encodes the navigation steps at call time; the value is the Head.Key.
	if rule.Head.Key != nil && len(rule.Head.Args) == 0 {
		v, ok := rule.Head.Key.Value.(ast.Var)
		if !ok {
			return nil, fmt.Errorf("contains rule head key is not a variable")
		}
		keyName := removeQuotes(v.String())
		tp, ok := t.TypeTrans.TypeInfo.Types[keyName]
		if !ok {
			return nil, verr.ErrTypeNotFound(keyName)
		}
		return []Arg{newPathArg(pathParamName), NewArg(keyName, tp)}, nil
	}

	args := make([]Arg, 0)
	for _, arg := range rule.Head.Args {
		name := removeQuotes(arg.String())
		tp, ok := t.TypeTrans.TypeInfo.Types[name]
		if !ok {
			return nil, verr.ErrTypeNotFound(name)
		}
		args = append(args, NewArg(name, tp))
	}
	return args, nil
}

// buildPathSmtValue constructs the SMT (Seq String) literal from the path elements
// in rule.Head.Ref()[1:].  Constant string elements are used directly as SMT string
// literals; variable elements are converted to String using type-aware extractors.
func buildPathSmtValue(rule *ast.Rule, exprTrans *ExprTranslator) (*SmtValue, error) {
	elems := make([]string, 0)
	for _, term := range rule.Head.Ref()[1:] {
		var elemStr string
		switch v := term.Value.(type) {
		case ast.String:
			// Constant string: use directly as a SMT string literal.
			elemStr = fmt.Sprintf("(seq.unit \"%s\")", string(v))
		case ast.Var:
			name := removeQuotes(v.String())
			tp, ok := exprTrans.TypeTrans.TypeInfo.Types[name]
			if !ok {
				return nil, verr.ErrTypeNotFound(name)
			}
			sv, err := exprTrans.termToSmtValue(term)
			if err != nil {
				return nil, err
			}
			// Convert OTypeD0 value to a String for (Seq String).
			var strPart string
			if tp.IsAtomic() && tp.AtomicType == types.AtomicString {
				strVal, err := sv.AsString()
				if err != nil {
					return nil, err
				}
				strPart = strVal.String()
			} else {
				intVal, err := sv.AsInt()
				if err != nil {
					return nil, fmt.Errorf("path element %s has unsupported type for Seq String", name)
				}
				strPart = fmt.Sprintf("(str.from_int %s)", intVal.String())
			}
			elemStr = fmt.Sprintf("(seq.unit %s)", strPart)
		default:
			return nil, fmt.Errorf("unsupported path element type %T in contains rule", term.Value)
		}
		elems = append(elems, elemStr)
	}

	var seqStr string
	switch len(elems) {
	case 0:
		seqStr = "(as seq.empty (Seq String))"
	case 1:
		seqStr = elems[0]
	default:
		seqStr = fmt.Sprintf("(seq.++ %s)", strings.Join(elems, " "))
	}
	return &SmtValue{value: seqStr, depth: seqArgDepth}, nil
}

// ruleOccurrenceToSmt is like ruleToSmtString but always uses OUndef as the else clause
// (never consults defaultsMap). Used for individual incremental rule occurrences; the
// default is applied at the combinator level by IncrementalRulesToSmt.
func (t *Translator) ruleOccurrenceToSmt(rule *ast.Rule) (*SmtValue, *SmtValue, error) {
	return t.ruleToSmtCore(rule, func(_ string, depth int) (*SmtValue, error) {
		return NewSmtValue("OUndef", 0).WrapToDepth(depth), nil
	})
}

// IncrementalRulesToSmt translates multiple Rego rules sharing the same name into SMT-LIB.
//
// Each rule occurrence i is emitted as a unique function `name_i`. A top-level combinator
// then chains them with nested ite: if name_1 is not OUndef use it, else try name_2, …,
// falling back to the declared default (or OUndef when no default is set).
//
// For 0-arg rules the combinator is an assertion (= name combinator); for rules with
// arguments it is a define-fun that shadows the per-occurrence functions.
func (t *Translator) IncrementalRulesToSmt(name string, rules []*ast.Rule) error {
	if len(rules) == 0 {
		return nil
	}

	// Combinatorargs come from rule 0; all occurrences must have the same arity.
	combinatorArgs, err := t.getArgs(rules[0])
	if err != nil {
		return err
	}

	occurrenceNames := make([]string, len(rules))
	retDepth := 0

	for i, rule := range rules {
		occName := t.FreshName(name)
		occurrenceNames[i] = occName

		// Each occurrence may use different OPA-generated local names for its
		// parameters (e.g. __local0__ vs __local1__), so fetch args per-occurrence.
		occArgs, err := t.getArgs(rule)
		if err != nil {
			return err
		}

		_, smtVal, err := t.ruleOccurrenceToSmt(rule)
		if err != nil {
			return err
		}
		retDepth = smtVal.depth

		smtName := t.applyPrefix(occName)
		t.smtDecls = append(t.smtDecls, DefineFun(smtName, occArgs, smtVal))
		t.Metadata.RuleGroups[t.applyPrefix(name)] = append(t.Metadata.RuleGroups[t.applyPrefix(name)], smtName)
	}

	// Build combinator from right to left: start with default (or OUndef)
	defaultVal, err := t.GetDefaultValue(name)
	if err != nil {
		return err
	}
	combinator := defaultVal.WrapToDepth(retDepth)

	for i := len(occurrenceNames) - 1; i >= 0; i-- {
		occName := t.applyPrefix(occurrenceNames[i])

		var callExpr *SmtValue
		if len(combinatorArgs) == 0 {
			callExpr = NewSmtValue(occName, retDepth)
		} else {
			argNames := make([]string, len(combinatorArgs))
			for j, arg := range combinatorArgs {
				argNames[j] = arg.name
			}
			callExpr = NewSmtValue(fmt.Sprintf("(%s %s)", occName, strings.Join(argNames, " ")), retDepth)
		}

		combinator = Ite(callExpr.IsUndef().Not(), callExpr, combinator)
	}

	if len(combinatorArgs) == 0 {
		varSmt := NewSmtValue(name, retDepth)
		t.smtAsserts = append(t.smtAsserts, Assert(varSmt.Equals(combinator)))
	} else {
		t.smtDecls = append(t.smtDecls, DefineFun(t.applyPrefix(name), combinatorArgs, combinator))
	}

	return nil
}

// RuleToSmt converts a Rego rule to an SMT-LIB assertion and appends it to the Translator's smtLines.
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule to convert.
//
// Returns:
//
//	error: An error if the rule cannot be converted.
//
// The rule variable (rule.Head.Name) is equal to the rule value (rule.Head.Value) if and only if all body expressions hold.
// The assertion is of the form: (assert (<=> (= ruleVar ruleValue) (and bodyExpr1 ... bodyExprN)))
func (t *Translator) RuleToSmt(rule *ast.Rule) error {
	name, value, err := t.ruleToSmtString(rule)
	if err != nil {
		return err
	}

	if rule.Default {
		return t.SetDefaultValue(name.String(), value)
	}

	args, err := t.getArgs(rule)
	if err != nil {
		return err
	}

	if len(args) == 0 {
		t.smtAsserts = append(t.smtAsserts, Assert(name.Equals(value)))
	} else {
		smtName := t.applyPrefix(name.String())
		t.smtDecls = append(t.smtDecls, DefineFun(smtName, args, value))
		t.Metadata.RuleGroups[smtName] = []string{smtName}
	}

	return nil
}
