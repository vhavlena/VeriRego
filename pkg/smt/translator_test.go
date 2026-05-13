package smt

import (
	"reflect"
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
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

	default allow := false

	allow contains output if {
		input.x == 1
		output := input.y
	}

	deny_param1 if {
		param1 := "foo"
	}

	deny_param2(b,c) if {
		param2 := "bar"
	}

	complex_rule_a(a) if {
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
	p := x if {
		x == 1
		x > 0
	}
	q := 42 if { true }
	`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	// Minimal type analyzer for variables used in rules
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"x":    types.NewAtomicType(types.AtomicInt),
			"p":    types.NewAtomicType(types.AtomicInt),
			"q":    types.NewAtomicType(types.AtomicInt),
			"true": types.NewAtomicType(types.AtomicBoolean),
		},
		Refs: map[string]ast.Value{},
	}
	tr := NewTranslator(ta, mod)
	tr.smtDecls = make([]*SmtCommand, 0) // remove default decls
	err = tr.TranslateModuleToSmt()
	if err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	smtLines := tr.SmtLines()
	assertCount := 0
	for i, line := range smtLines {
		if line == "" || line[:7] != "(assert" {
			t.Errorf("SMT line %d not an assertion: %q", i, line)
			continue
		}
		assertCount++
	}
	if assertCount != 2 {
		t.Errorf("Expected 2 SMT assertions, got %d", assertCount)
	}
}

func TestTranslateModuleToSmt_Trim(t *testing.T) {
	t.Run("literal second argument", func(t *testing.T) {
		rego := `
		package test
		allow if {
			trim(input.name, " ") == "foo"
		}
		`
		mod, err := ast.ParseModule("trim.rego", rego)
		if err != nil {
			t.Fatalf("failed to parse rego: %v", err)
		}

		ta := &types.TypeAnalyzer{
			Types: map[string]types.RegoTypeDef{
				"input": types.NewObjectType(map[string]types.RegoTypeDef{
					"name": types.NewAtomicType(types.AtomicString),
				}),
				"allow": types.NewAtomicType(types.AtomicBoolean),
			},
			Refs: map[string]ast.Value{},
		}

		tr := NewTranslator(ta, mod)
		if err := tr.TranslateModuleToSmt(); err != nil {
			t.Fatalf("TranslateModuleToSmt error: %v", err)
		}

		smt := strings.Join(tr.SmtLines(), "\n")
		if !strings.Contains(smt, "(declare-fun trim (String String) String)") {
			t.Fatalf("expected trim declaration in SMT, got:\n%s", smt)
		}
		if !strings.Contains(smt, "(trim ") {
			t.Fatalf("expected trim uninterpreted function in SMT, got:\n%s", smt)
		}
		if !strings.Contains(smt, `" "`) {
			t.Fatalf("expected literal trim chars in SMT, got:\n%s", smt)
		}
	})

	t.Run("non-literal second argument", func(t *testing.T) {
		rego := `
		package test
		allow if {
			trim(input.name, input.name) == "foo"
		}
		`
		mod, err := ast.ParseModule("trim_invalid.rego", rego)
		if err != nil {
			t.Fatalf("failed to parse rego: %v", err)
		}

		ta := &types.TypeAnalyzer{
			Types: map[string]types.RegoTypeDef{
				"input": types.NewObjectType(map[string]types.RegoTypeDef{
					"name": types.NewAtomicType(types.AtomicString),
				}),
				"allow": types.NewAtomicType(types.AtomicBoolean),
			},
			Refs: map[string]ast.Value{},
		}

		tr := NewTranslator(ta, mod)
		if err := tr.TranslateModuleToSmt(); err == nil {
			t.Fatal("expected TranslateModuleToSmt to fail for non-literal trim chars")
		} else if !strings.Contains(err.Error(), "string literal") {
			t.Fatalf("expected string-literal error, got: %v", err)
		}
	})
}

// TestGetSmtVarsDeclare_SkipsFunctionTypes verifies that KindFunction entries in
// the type map are excluded from the set of global SMT variables to declare.
// User-defined functions contribute a KindFunction entry to the TypeAnalyzer —
// including them would cause GenerateVarDecl to fail with ErrUnsupportedType.
func TestGetSmtVarsDeclare_SkipsFunctionTypes(t *testing.T) {
	t.Parallel()
	rego := `package test
add_one(x) := y if { y := x + 1 }
p := z if { z := 1 }
`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}

	ta := types.NewTypeAnalyzerWithParams(mod.Package.Path, types.NewInputSchema())
	ta.AnalyzeModule(mod)

	tr := NewTranslator(ta, mod)
	globalVars := tr.getSmtVarsDeclare()

	// "add_one" must be absent – it is a KindFunction entry, not a variable.
	if _, found := globalVars["add_one"]; found {
		t.Error("KindFunction entry 'add_one' should not appear in globalVars for SMT declaration")
	}
}
