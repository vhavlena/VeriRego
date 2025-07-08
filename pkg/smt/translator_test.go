package smt

import (
	"reflect"
	"testing"

	"github.com/open-policy-agent/opa/ast"
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
