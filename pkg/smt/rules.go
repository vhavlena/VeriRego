package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
)

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

func (t *Translator) RuleToSmtString(rule *ast.Rule) (string,error) {
	if rule == nil {
		return "true",nil
	}
	println(" RuleToSmtString: ", rule.String())
	// get head
	exprTrans := NewExprTranslatorWithVarMap(t.TypeTrans, t.VarMap)
	smtHead, err := t.ruleHeadToSmt(rule, exprTrans)
	if err != nil {
		return "",err
	}

	// Convert all body expressions to SMT
	bodySmts := make([]string, 0, len(rule.Body))
	for _, expr := range rule.Body {
		smtStr, err := exprTrans.ExprToSmt(expr)
		if err != nil {
			return "",fmt.Errorf("failed to convert rule body expr: %w", err)
		}
		bodySmts = append(bodySmts, smtStr)
	}
	t.AddTransContext(exprTrans.GetTransContext())
	bodySmt := fmt.Sprintf("(and %s)", strings.Join(bodySmts, " "))

	// get else
	elseSmt, err := t.RuleToSmtString(rule.Else)
	if err != nil {
		return "",err
	}

	// return
	smt := fmt.Sprintf("(ite %s %s %s)", bodySmt, smtHead, elseSmt)
	println(" returns ", smt)
	return smt,nil
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
	println("RuleToSmt: ", rule.String())
	smt,err := t.RuleToSmtString(rule)
	if err != nil {
		return err
	}

	assertion := fmt.Sprintf("(assert %s)", smt)
	t.smtAsserts = append(t.smtAsserts, assertion)
	return nil
}
