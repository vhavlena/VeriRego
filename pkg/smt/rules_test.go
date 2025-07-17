package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

func TestRuleToSmt_Basic(t *testing.T) {
	rego := `
	package test
	p = x {
		x == 1
		x > 0
	}`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
			"p": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{},
	}
	tr := &Translator{TypeInfo: ta, smtLines: make([]string, 0, 8)}
	rule := mod.Rules[0]
	err = tr.RuleToSmt(rule)
	if err != nil {
		t.Fatalf("RuleToSmt error: %v", err)
	}
	if len(tr.smtLines) == 0 {
		t.Fatalf("No SMT lines generated")
	}
	got := tr.smtLines[len(tr.smtLines)-1]
	if got == "" || got[:7] != "(assert" {
		t.Errorf("Expected SMT assertion, got: %q", got)
	}
}

func TestRuleToSmt_NoBody(t *testing.T) {
	rego := `
	package test
	p = 42 { true }`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"p": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{},
	}
	tr := &Translator{TypeInfo: ta, smtLines: make([]string, 0, 8)}
	rule := mod.Rules[0]
	err = tr.RuleToSmt(rule)
	if err != nil {
		t.Fatalf("RuleToSmt error: %v", err)
	}
	got := tr.smtLines[len(tr.smtLines)-1]
	if got == "" || got[:7] != "(assert" {
		t.Errorf("Expected SMT assertion, got: %q", got)
	}
	if want := "true"; want != "" && !strings.Contains(got, want) {
		t.Errorf("Expected assertion to contain %q, got: %q", want, got)
	}
}
