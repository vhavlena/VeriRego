package smt

import (
	"fmt"
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

func TestRuleToSmt_Basic(t *testing.T) {
	rego := `
	package test
	p := x if {
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
	tr := NewTranslator(ta, mod)
	rule := mod.Rules[0]
	err = tr.RuleToSmt(rule)
	if err != nil {
		t.Fatalf("RuleToSmt error: %v", err)
	}
	lines := tr.SmtLines()
	if len(lines) == 0 {
		t.Fatalf("No SMT lines generated")
	}
	got := lines[len(lines)-1]
	if got == "" || got[:7] != "(assert" {
		t.Errorf("Expected SMT assertion, got: %q", got)
	}
}

func TestRuleToSmt_NoBody(t *testing.T) {
	rego := `
	package test
	p := 42 if { true }`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"p": types.NewAtomicType(types.AtomicInt),
			"true": types.NewAtomicType(types.AtomicBoolean),
		},
		Refs: map[string]ast.Value{},
	}
	tr := NewTranslator(ta, mod)
	rule := mod.Rules[0]
	err = tr.RuleToSmt(rule)
	if err != nil {
		t.Fatalf("RuleToSmt error: %v", err)
	}
	lines := tr.SmtLines()
	if len(lines) == 0 {
		t.Fatalf("No SMT lines generated")
	}
}

// TestIncrementalRules_NoDefault checks that two incremental rules (same name, no default)
// produce one define-fun per occurrence plus a combinator assert using nested ite.
func TestIncrementalRules_NoDefault(t *testing.T) {
	rego := `
	package test
	p := 1 if { input_x == 1 }
	p := 2 if { input_x == 2 }`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"p":       types.NewAtomicType(types.AtomicInt),
			"input_x": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{},
	}
	tr := NewTranslator(ta, mod)
	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	lines := tr.SmtLines()
	joined := strings.Join(lines, "\n")

	// Expect occurrence functions p_1 and p_2
	for _, occName := range []string{"p_1", "p_2"} {
		if !strings.Contains(joined, fmt.Sprintf("(define-fun %s", occName)) {
			t.Errorf("expected define-fun for %s, got:\n%s", occName, joined)
		}
	}
	// Expect a combinator assertion referencing p_1 and p_2 via is-OUndef
	if !strings.Contains(joined, "is-OUndef") {
		t.Errorf("expected is-OUndef in combinator, got:\n%s", joined)
	}
	// Expect a top-level assertion for p
	if !strings.Contains(joined, "(assert") {
		t.Errorf("expected assert for p combinator, got:\n%s", joined)
	}
}

// TestIncrementalRules_WithDefault checks that the default value appears as the fallback
// in the combinator when a default rule is declared.
func TestIncrementalRules_WithDefault(t *testing.T) {
	rego := `
	package test
	default p := 0
	p := 1 if { input_x == 1 }
	p := 2 if { input_x == 2 }`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"p":       types.NewAtomicType(types.AtomicInt),
			"input_x": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{},
	}
	tr := NewTranslator(ta, mod)
	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	lines := tr.SmtLines()
	joined := strings.Join(lines, "\n")

	for _, occName := range []string{"p_1", "p_2"} {
		if !strings.Contains(joined, fmt.Sprintf("(define-fun %s", occName)) {
			t.Errorf("expected define-fun for %s, got:\n%s", occName, joined)
		}
	}
	// The combinator should fall back to 0 (the default), not OUndef
	if !strings.Contains(joined, "ONumber") {
		t.Errorf("expected default ONumber value in combinator, got:\n%s", joined)
	}
}

// TestIncrementalRules_FunctionArgs checks incremental rules that take arguments
// produce define-fun occurrences and a top-level define-fun combinator.
func TestIncrementalRules_FunctionArgs(t *testing.T) {
	rego := `
	package test
	f(x) := 1 if { x == 1 }
	f(x) := 2 if { x == 2 }`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"f": types.NewFunctionType(
				"f",
				[]types.RegoTypeDef{types.NewAtomicType(types.AtomicInt)},
				types.NewAtomicType(types.AtomicInt),
			),
			"x": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{},
	}
	tr := NewTranslator(ta, mod)
	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	lines := tr.SmtLines()
	joined := strings.Join(lines, "\n")

	for _, occName := range []string{"f_1", "f_2"} {
		if !strings.Contains(joined, fmt.Sprintf("(define-fun %s", occName)) {
			t.Errorf("expected define-fun for %s, got:\n%s", occName, joined)
		}
	}
	// Top-level combinator define-fun for f
	if !strings.Contains(joined, "(define-fun f ") {
		t.Errorf("expected top-level define-fun for f, got:\n%s", joined)
	}
}

func TestRuleToSmt_LocalVars(t *testing.T) {
	rego := `
	package test
	p := 1 if {
		x = 1
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
	tr := NewTranslator(ta, mod)
	rule := mod.Rules[0]
	err = tr.RuleToSmt(rule)
	if err != nil {
		t.Fatalf("RuleToSmt error: %v", err)
	}
	lines := tr.SmtLines()
	if len(lines) == 0 {
		t.Fatalf("No SMT lines generated")
	}
	got := lines[len(lines)-1]
	if !strings.Contains(got, "(assert ") || !strings.Contains(got, "(let ")  {
		t.Errorf("Expected SMT assertion with let expression, got: %q", got)
	}
}
