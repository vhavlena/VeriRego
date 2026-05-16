package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
)

// ruleHeadValueSmt returns smt values for a rule variable and its corresponding value
//
// Returns:
//
//	*SmtValue: variable
//	*SmtValue: value
//	error
func (t *Translator) ruleHeadValueSmt(rule *ast.Rule, exprTrans *ExprTranslator) (*SmtValue, *SmtValue, error) {
	if rule == nil || rule.Head == nil {
		return nil, nil, fmt.Errorf("invalid rule: nil head")
	}
	ruleVar, err := NewSmtValueFromVar(rule.Head.Name, exprTrans)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to convert rule head value: %w", err)
	}
	// FIXME: add `contains` support
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

	bodySmt, localVarDefs, err := exprTrans.BodyToSmt(&rule.Body)
	if err != nil {
		return nil, nil, err
	}
	t.AddTransContext(exprTrans.GetTransContext())

	name := rule.Head.Name.String()
	depth := 0
	if tp, ok := t.TypeTrans.TypeInfo.Types[name]; ok {
		depth = max(tp.TypeDepth(), 0)
	}

	var elseSmt *SmtValue
	if rule.Else != nil {
		_, elseSmt, err = t.ruleToSmtCore(rule.Else, getDefault)
		if err != nil {
			return nil, nil, err
		}
	} else {
		elseSmt, err = getDefault(name, depth)
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
