package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/smt/factory"
)

// ruleHeadToSmt converts the head of a Rego rule to its SMT-LIB representation (including the operator).
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule whose head is to be converted.
//	exprTrans *ExprTranslator: The expression translator to use for converting terms and references.
//
// Returns:
//
//	smtHead string: The SMT-LIB representation of the rule head (e.g., (= var val)).
//	error: An error if the head cannot be converted.
func (t *Translator) ruleHeadToSmt(rule *ast.Rule, exprTrans *ExprTranslator) (string, error) {
	if rule == nil || rule.Head == nil {
		return "", fmt.Errorf("invalid rule: nil head")
	}
	ruleVar := rule.Head.Name.String()
	ruleVarSmt, err := t.TypeTrans.getVarValue(ruleVar)
	if err != nil {
		return "", fmt.Errorf("failed to get SMT var for rule head %s: %w", ruleVar, err)
	}
	// TODO: simplification: violation[result] should be converted to violation contains result
	// for now, we translate it to violation = result (assume only singletons)
	if rule.Head.Value == nil {
		if rule.Head.Key != nil && rule.Head.Reference != nil {
			var err error
			if ruleVar, err = exprTrans.termToSmt(rule.Head.Key); err != nil {
				return "", fmt.Errorf("failed to convert rule head key: %w", err)
			}
			ruleValSmt, err := exprTrans.refToSmt(rule.Head.Reference)
			if err != nil {
				return "", fmt.Errorf("failed to convert rule head reference: %w", err)
			}
			return fmt.Sprintf("(= %s %s)", ruleVarSmt, ruleValSmt), nil
		}
		return "", fmt.Errorf("rule head value is nil for %s", ruleVar)
	}
	ruleValSmt, err := exprTrans.termToSmt(rule.Head.Value)
	if err != nil {
		return "", fmt.Errorf("failed to convert rule head value: %w", err)
	}
	return fmt.Sprintf("(= %s %s)", ruleVarSmt, ruleValSmt), nil
}

// BodyToSmt converts the body of a Rego rule into SMT-LIB representation 1. of the expression, and 2. of local variables definition
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule whose body is to be converted.
//	exprTrans *ExprTranslator: The expression translator to use for converting terms and references.
//
// Returns:
//
//	bodySmt string: The SMT-LIB representation of the rule body (e.g., (and expr1 expr2 ...)).
//	localVarDef string: The SMT-LIB representation of local variables definition
//	error: An error if the body cannot be converted.
func (t *Translator) BodyToSmt(rule *ast.Rule, exprTrans *ExprTranslator) (string, string, error) {
	bodySmts := make([]string, 0, len(rule.Body))
	localVarDefs := make([]string, 0)

	for _, expr := range rule.Body {
		smtStr, localVarDef, err := exprTrans.ExprToSmtWithInfo(expr)
		if err != nil {
			return "", "", fmt.Errorf("failed to convert rule body expr: %w", err)
		}
		bodySmts = append(bodySmts, smtStr)
		if localVarDef != "" {
			localVarDefs = append(localVarDefs, localVarDef)
		}
	}
	t.AddTransContextAndAsserts(exprTrans.GetTransContext())	// TODO ask: why doing this?

	var bodySmt string
	switch len(bodySmts) {
	case 0:
		bodySmt = "true"
	case 1:
		bodySmt = bodySmts[0]
	default:
		bodySmt = fmt.Sprintf("(and %s)", strings.Join(bodySmts, " "))
	}
	rule.Ref()
	return bodySmt, strings.Join(localVarDefs, " "), nil
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
// The rule variable (rule.Head.Name) is equal to the rule value (rule.Head.Value) if and only if all body expressions hold. It is equal to the else value otherwise (or Undef, if no else branch is suitable)
func (t *Translator) RuleToSmt(rule *ast.Rule) (string,error) {
	exprTrans := NewExprTranslatorWithVarMapAndDecls(t.TypeTrans, t.VarMap, t.smtDecls)
	smtHead, err := t.ruleHeadToSmt(rule, exprTrans)
	if err != nil {
		return "", err
	}

	bodySmt, localVarDef, err := t.BodyToSmt(rule, exprTrans)
	if err != nil {
		return "", err
	}

	elseValue := ""
	if rule.Else != nil {
		elseValue, err = t.RuleToSmt(rule.Else)
		if err != nil {
			return "", err
		}
	} else {
		elseValue = fmt.Sprintf("(is-OUndef (atom %s))", rule.Head.Name.String())
	}
	smt := fmt.Sprintf("(ite %s %s %s)", bodySmt, smtHead, elseValue)
	if localVarDef != "" {
		return factory.Let(&localVarDef, &smt), nil
	} else {
		return smt, nil
	}
}

// ParametricRuleToSmt converts a parametric Rego rule to an SMT-LIB representation. 
// The output is expected to be appended to smtLines as a function definition.
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule to convert.
//
// Returns:
//
//	smt string: The SMT-LIB representation of rule.
//	error: An error if the rule cannot be converted.
//
// The rule value is returned iff all body expression hold. If not, its else value is returned.
// For empty else value, the Undef value is returned.
func (t *Translator) ParametricRuleToSmt(rule *ast.Rule) (string,error) {
	if rule == nil {
		return "undefined", nil	// FIXME: return correct SMT undefined value
	}
	exprTrans := NewExprTranslatorWithVarMapAndDecls(t.TypeTrans, t.VarMap, t.smtDecls)
	// Get head value
	var smtValue string
	if rule.Head.Value == nil {
		if rule.Head.Key != nil && rule.Head.Reference != nil {
			var err error
			smtValue, err = exprTrans.refToSmt(rule.Head.Reference)
			if err != nil {
				return "", fmt.Errorf("failed to convert rule head reference: %w", err)
			}
		}
		return "", fmt.Errorf("rule head value is nil for %s", rule.Head.String())
	} else {
		var err error
		smtValue, err = exprTrans.termToSmt(rule.Head.Value)
		if err != nil {
			return "", fmt.Errorf("failed to convert rule head value: %w", err)
		}
	}

	bodySmt, localVarDef, err := t.BodyToSmt(rule, exprTrans)
	if err != nil {
		return "", err
	}

	if localVarDef != "" {
		// TODO
	}

	elseValue, err := t.ParametricRuleToSmt(rule.Else)
	if err != nil {
		return "", err
	}
	smt := fmt.Sprintf("(ite %s %s %s)", bodySmt, smtValue, elseValue)
	return smt, nil
}

// RuleToAssert converts a Rego rule to an SMT-LIB assertion and appends it to smtLines. 
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule to convert.
//
// Returns:
//
//	error: An error if the rule cannot be converted.
//
// For parametric rules, the assertion is a function definition (appended to smtDecls)
// Otherwise, it is an assignment (appended to smtAsserts)
func (t *Translator) RuleToAssert(rule *ast.Rule) error {
	if len(rule.Head.Args) == 0 {
		smt, err := t.RuleToSmt(rule)
		if err != nil {
			return err
		}
		assertion := fmt.Sprintf("(assert %s)", smt)
		t.smtAsserts = append(t.smtAsserts, assertion)
		return nil
	}
	// Parametric rule
	funcName := rule.Head.Name.String()
	a := rule.Head.Args
	args := make([]string, 0, len(a))
	for _, t := range a {
		args = append(args, "(" + t.String() + " OType)")
	}
	argList := "(" + strings.Join(args, " ") + ")"
	retType := "OType"
	
	funcBody, err := t.ParametricRuleToSmt(rule)
	if err != nil {
		return err
	}
	funcDef := fmt.Sprintf("(define-fun %s %s %s %s)", funcName, argList, retType, funcBody)
	t.smtDecls = append(t.smtDecls, funcDef)
	return nil
}
