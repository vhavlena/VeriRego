package smt

import (
	"reflect"
	"testing"

	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

func TestInputParameterVars(t *testing.T) {
	rule := &ast.Rule{
		Head: &ast.Head{
			Args: []*ast.Term{
				ast.VarTerm("input1"),
				ast.VarTerm("input2"),
			},
		},
	}
	mod := &ast.Module{
		Rules: []*ast.Rule{rule},
	}
	tr := &Translator{mod: mod}
	got := tr.InputParameterVars()
	want := []string{"input1", "input2"}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("InputParameterVars() = %v, want %v", got, want)
	}
}

func TestInputParameterVars_Empty(t *testing.T) {
	tr := &Translator{mod: &ast.Module{Rules: nil}}
	if got := tr.InputParameterVars(); got != nil && len(got) != 0 {
		t.Errorf("Expected nil or empty, got %v", got)
	}
}

func TestInputParameterVars_NilModule(t *testing.T) {
	tr := &Translator{mod: nil}
	if got := tr.InputParameterVars(); got != nil && len(got) != 0 {
		t.Errorf("Expected nil or empty, got %v", got)
	}
}

func TestInputParameterVars_FromRegoPolicyString(t *testing.T) {
	t.Parallel()
	rego := `
package test

default allow = false

allow[output] {
	input.x == 1
	output := input.y
}

deny_param1 {
	param1 := "foo"
}

deny_param2(b,c) {
	param2 := "bar"
}

complex_rule_a(a) {
	a := input.a
}
`

	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("Failed to parse module: %v", err)
	}
	tr := &Translator{mod: mod}
	got := tr.InputParameterVars()
	want := []string{"b", "c", "a"}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("InputParameterVars() = %v, want %v", got, want)
	}
}

func TestTranslateModuleToSmt_Basic(t *testing.T) {
	rego := `
	package test
	p = x {
		x == 1
		x > 0
	}
	q = 42 { true }
	`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	// Minimal type analyzer for variables used in rules
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
			"p": types.NewAtomicType(types.AtomicInt),
			"q": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{},
	}
	tr := NewTranslator(ta, mod)
	err = tr.TranslateModuleToSmt()
	if err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	smtLines := tr.SmtLines()
	if len(smtLines) != 2 {
		t.Errorf("Expected 2 SMT assertions, got %d", len(smtLines))
	}
	for i, line := range smtLines {
		if line == "" || line[:7] != "(assert" {
			t.Errorf("SMT line %d not an assertion: %q", i, line)
		}
	}
}
