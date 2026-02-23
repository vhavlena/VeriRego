package smt

import (
	"fmt"

	"github.com/open-policy-agent/opa/v1/ast"
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

func (t *Translator) ruleHeadValueSmt(rule *ast.Rule, exprTrans *ExprTranslator) (string,string,error) {
	if rule == nil || rule.Head == nil {
		return "","", fmt.Errorf("invalid rule: nil head")
	}
	ruleVar := rule.Head.Name.String()
	ruleValSmt, err := exprTrans.termToSmtValue(rule.Head.Value)		// TODO: tweak functionality of termToSmt
	if err != nil {
		return "","", fmt.Errorf("failed to convert rule head value: %w", err)
	}
	return ruleVar,ruleValSmt, nil
}

func (t *Translator) ruleToSmtStringWithHead(rule *ast.Rule) (string,string,error) {
	// get head
	exprTrans := NewExprTranslatorWithVarMap(t.TypeTrans, t.VarMap)
	smtHead, smtVal, err := t.ruleHeadValueSmt(rule, exprTrans)
	if err != nil {
		return "","",err
	}

	bodySmt,localVarsDef,err := exprTrans.BodyToSmt(&rule.Body)
	if err != nil {
		return "","",err
	}
	t.AddTransContext(exprTrans.GetTransContext())

	// get else
	name := rule.Head.Name.String()
	elseVal, err := t.GetDefaultValue(name)
	if err != nil {
		return "","",err
	}
	elseSmt := elseVal.String()	// TODO: work with SmtValues
	if rule.Else != nil {
		_,elseSmt, err = t.ruleToSmtStringWithHead(rule.Else)
		if err != nil {
			return "","",err
		}
	}

	// return
	smt := fmt.Sprintf("(ite %s %s %s)", bodySmt, smtVal, elseSmt)
	if localVarsDef != "" {
		smt = fmt.Sprintf("(let %s %s)", localVarsDef, smt)
	}
	return smtHead,smt,nil
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
	name,smt,err := t.ruleToSmtStringWithHead(rule)
	if err != nil {
		return err
	}

	// TODO get args

	assertion := Assert(RawProposition(fmt.Sprintf("(= %s %s)", name, smt)))
	t.smtAsserts = append(t.smtAsserts, assertion)
	return nil
}
