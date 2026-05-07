package smt

import (
	"fmt"

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

// ruleToSmtString returns smt values for a rule variable and for its assignment based on the rule
//
// Returns:
//
//	*SmtValue: variable
//	*SmtValue: assignment - value, which is conditional to the rule body
//	error
func (t *Translator) ruleToSmtString(rule *ast.Rule) (*SmtValue, *SmtValue, error) {
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
	elseVal, err := t.GetDefaultValue(name)
	if err != nil {
		return nil, nil, err
	}
	elseSmt := elseVal
	if rule.Else != nil {
		_, elseSmt, err = t.ruleToSmtString(rule.Else)
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

	// Collect body for entry-point aggregation before emitting individual assertions.
	if t.entryPoint != "" && rule.Head.Name.String() == t.entryPoint {
		t.entryPointBodies = append(t.entryPointBodies, value)
	}

	smtSymbolName := t.prefix + name.String()
	smtSymbol := NewSmtValue(smtSymbolName, name.GetDepth())

	args, err := t.getArgs(rule)
	if err != nil {
		return err
	}

	if len(args) == 0 {
		assertion := Assert(smtSymbol.Equals(value))
		t.smtAsserts = append(t.smtAsserts, assertion)
	} else {
		fun := DefineFun(smtSymbolName, args, value)
		t.smtDecls = append(t.smtDecls, fun)
	}

	return nil
}
