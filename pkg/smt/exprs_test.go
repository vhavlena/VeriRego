package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/types"
)

func newDummyExprTranslator() *ExprTranslator {
	// Setup a dummy type analyzer with some schema variables.
	// The root key is "input" (the new architecture); nested fields are
	// accessed via the path resolution in refToSmtValue.
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"data": types.NewObjectType(map[string]types.RegoTypeDef{
					"x": types.NewObjectType(map[string]types.RegoTypeDef{
						"y": types.NewAtomicType(types.AtomicBoolean),
					}),
				}),
			}),
		},
		Refs: map[string]ast.Value{},
	}
	typeTrans := NewTypeDefs(ta)
	return NewExprTranslator(typeTrans)
}

func newTestExprTranslatorWithTypes(typeMap map[string]types.RegoTypeDef) *ExprTranslator {
	ta := &types.TypeAnalyzer{
		Types: typeMap,
		Refs:  map[string]ast.Value{},
	}
	typeTrans := NewTypeDefs(ta)
	return NewExprTranslator(typeTrans)
}

func newDummyTranslator() *Translator {
	// Setup a dummy type analyzer with some schema variables.
	// The root key is "input" (the new architecture).
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"data": types.NewObjectType(map[string]types.RegoTypeDef{
					"x": types.NewObjectType(map[string]types.RegoTypeDef{
						"y": types.NewAtomicType(types.AtomicBoolean),
					}),
				}),
			}),
		},
		Refs: map[string]ast.Value{},
	}
	return NewTranslator(ta, nil)
}

// TestTermToSmtValue_Ref exercises the ast.Ref branch of termToSmtValue.
// After the refactoring, input.* and data.* refs resolve through the object
// root ("input" / "data") rather than per-field type entries, producing
// proper SMT select expressions that are valid Z3.
func TestTermToSmtValue_Ref(t *testing.T) {
	t.Parallel()

	t.Run("InputRefAtomic", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"role": types.NewAtomicType(types.AtomicString),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.role")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		if val == nil {
			t.Fatal("expected non-nil SmtValue")
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "role")) {
			t.Errorf("expected select expression over 'input' accessing 'role', got %q", s)
		}
	})

	t.Run("InputRefInt", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"count": types.NewAtomicType(types.AtomicInt),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.count")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "count")) {
			t.Errorf("expected select expression over 'input' accessing 'count', got %q", s)
		}
	})

	t.Run("InputRefBoolean", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"active": types.NewAtomicType(types.AtomicBoolean),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.active")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "active")) {
			t.Errorf("expected select expression over 'input' accessing 'active', got %q", s)
		}
	})

	t.Run("InputRefMissingType", func(t *testing.T) {
		t.Parallel()
		// Neither "input" nor "input.x" is in the type map — must error.
		typeMap := map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.x")
		_, err := et.termToSmtValue(term)
		if err == nil {
			t.Error("expected error for missing 'input' type, got nil")
		}
	})

	t.Run("DataRefAtomic", func(t *testing.T) {
		t.Parallel()
		dataSchema := types.NewInputJsonSchema()
		typeMap := map[string]types.RegoTypeDef{
			"data": types.NewObjectType(map[string]types.RegoTypeDef{
				"token": types.NewAtomicType(types.AtomicString),
			}),
		}
		ta := &types.TypeAnalyzer{
			Types:      typeMap,
			Refs:       map[string]ast.Value{},
			DataSchema: dataSchema,
		}
		et := NewExprTranslator(NewTypeDefs(ta))
		term := ast.MustParseTerm("data.token")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "data") && strings.Contains(s, "token")) {
			t.Errorf("expected select expression over 'data' accessing 'token', got %q", s)
		}
	})

	t.Run("VarRefObj", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"count": types.NewAtomicType(types.AtomicInt),
			}),
			"str": types.NewAtomicType(types.AtomicString),
			"int": types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input[str]")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "obj") && strings.Contains(s, "str")) {
			t.Errorf("expected select expression over object 'input', got %q", s)
		}
		if val.GetDepth() != 0 {
			t.Errorf("expected \"%s\" to have depth 0, got %d", s, val.GetDepth())
		}
		if !val.TypeIs(types.AtomicInt) {
			t.Errorf("expected \"%s\" to have type Int", s)
		}
		term = ast.MustParseTerm("input[int]")
		val, err = et.termToSmtValue(term)
		if err == nil {
			t.Errorf("accessing object with integer key should fail, got %q", val.String())
		}
	})

	t.Run("VarRefInt", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewArrayType(types.NewAtomicType(types.AtomicInt)),
			"str": types.NewAtomicType(types.AtomicString),
			"int": types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input[int]")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "seq.nth") && strings.Contains(s, "input") && strings.Contains(s, "arr") && strings.Contains(s, "int")) {
			t.Errorf("expected seq.nth expression over array 'input', got %q", s)
		}
		if val.GetDepth() != 0 {
			t.Errorf("expected \"%s\" to have depth 0, got %d", s, val.GetDepth())
		}
		if !val.TypeIs(types.AtomicInt) {
			t.Errorf("expected \"%s\" to have type Int", s)
		}
		term = ast.MustParseTerm("input[str]")
		val, err = et.termToSmtValue(term)
		if err == nil {
			t.Errorf("accessing array with string key should fail, got %q", val.String())
		}
	})
}

// generateSMT is a test helper that runs the compile → inline → type-infer →
// SMT-translate pipeline and returns the raw SMT-LIB string.
func generateSMT(t *testing.T, regoSrc string, jsonSchema []byte) string {
	t.Helper()
	mod, err := ast.ParseModuleWithOpts("p.rego", regoSrc, ast.ParserOptions{RegoVersion: ast.RegoV1})
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{mod.Package.Path.String(): mod})
	if compiler.Failed() {
		t.Fatalf("compile error: %v", compiler.Errors)
	}
	compiledModule := compiler.Modules[mod.Package.Path.String()]

	inliner := simplify.NewInliner()
	inliner.GatherInlinePredicates(compiledModule)
	compiledModule = inliner.InlineModule(compiledModule)

	inputSchema := types.InputSchemaAPI(types.NewInputJsonSchema())
	if len(jsonSchema) > 0 {
		js := types.NewInputJsonSchema()
		if err := js.ProcessInput(jsonSchema); err != nil {
			t.Fatalf("json schema error: %v", err)
		}
		inputSchema = js
	}

	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema)
	typeAnalyzer.AnalyzeModule(compiledModule)

	translator := NewTranslator(typeAnalyzer, compiledModule)
	if err := translator.GenerateSmtContent(); err != nil {
		t.Fatalf("smt generation error: %v", err)
	}
	return strings.Join(translator.SmtLines(), "\n")
}

func TestAllowIfSyntax_NotDroppedByInliner(t *testing.T) {
	for _, rego := range []struct{ name, src string }{
		{"allow if", `package example
default allow := false
allow if { 1 == 1 }`},
		{"allow := true if", `package example
default allow := false
allow := true if { 1 == 1 }`},
	} {
		t.Run(rego.name, func(t *testing.T) {
			smt := generateSMT(t, rego.src, nil)
			if !strings.Contains(smt, "(declare-fun allow ()") {
				t.Errorf("expected 'allow' declaration in SMT output (inliner may have dropped the rule):\n%s", smt)
			}
		})
	}
}
