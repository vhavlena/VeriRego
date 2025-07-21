package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/ast"
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
//
// Returns:
//
//	smtHead string: The SMT-LIB representation of the rule head (e.g., (= var val)).
//	error: An error if the head cannot be converted.
func (t *Translator) ruleHeadToSmt(rule *ast.Rule) (string, error) {
	if rule == nil || rule.Head == nil {
		return "", fmt.Errorf("invalid rule: nil head")
	}
	ruleVar := rule.Head.Name.String()
	// TODO: simplification: violation[result] should be converted to violation contains result
	// for now, we translate it to violation = result (assume only singletons)
	if rule.Head.Value == nil {
		if rule.Head.Key != nil && rule.Head.Reference != nil {
			var err error
			if ruleVar, err = t.termToSmt(rule.Head.Key); err != nil {
				return "", fmt.Errorf("failed to convert rule head key: %w", err)
			}
			ruleValSmt, err := t.refToSmt(rule.Head.Reference)
			if err != nil {
				return "", fmt.Errorf("failed to convert rule head reference: %w", err)
			}
			return fmt.Sprintf("(= %s %s)", ruleVar, ruleValSmt), nil
		}
		return "", fmt.Errorf("rule head value is nil for %s", ruleVar)
	}
	ruleValSmt, err := t.termToSmt(rule.Head.Value)
	if err != nil {
		return "", fmt.Errorf("failed to convert rule head value: %w", err)
	}
	return fmt.Sprintf("(= %s %s)", ruleVar, ruleValSmt), nil
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
	smtHead, err := t.ruleHeadToSmt(rule)
	if err != nil {
		return err
	}

	// Convert all body expressions to SMT
	bodySmts := make([]string, 0, len(rule.Body))
	for _, expr := range rule.Body {
		smtStr, err := t.exprToSmt(*expr)
		if err != nil {
			return fmt.Errorf("failed to convert rule body expr: %w", err)
		}
		bodySmts = append(bodySmts, smtStr)
	}
	var bodySmt string
	switch len(bodySmts) {
	case 0:
		bodySmt = "true"
	case 1:
		bodySmt = bodySmts[0]
	default:
		bodySmt = fmt.Sprintf("(and %s)", strings.Join(bodySmts, " "))
	}

	assertion := fmt.Sprintf("(assert (= %s %s))", smtHead, bodySmt)
	t.smtAsserts = append(t.smtAsserts, assertion)
	return nil
}
