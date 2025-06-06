package types

import (
	"fmt"
	"testing"

	"github.com/open-policy-agent/opa/ast"
)

func TestBasicTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "string literal",
			rule: `package test
test { x := "hello" }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "number literal",
			rule: `package test
test { x := 42 }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "boolean literal",
			rule: `package test
test { x := true }`,
			varName:  "x",
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "array literal",
			rule: `package test
test { x := ["a", "b"] }`,
			varName:  "x",
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "object literal",
			rule: `package test
test { x := {"key": "value"} }`,
			varName: "x",
			expected: NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			}),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			analyzer := AnalyzeTypes(module.Rules[0], schema)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestBuiltinFunctionTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "boolean function",
			rule: `package test
test { x=true }`,
			varName:  "x",
			expected: NewAtomicType(AtomicBoolean),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			analyzer := AnalyzeTypes(module.Rules[0], schema)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestInputSchemaBasedInference(t *testing.T) {
	t.Parallel()

	// Sample YAML input
	yamlInput := []byte(`
input:
  review:
    object:
      kind: "Pod"
      metadata:
        name: "test-pod"
      spec:
        containers:
          - name: "container1"
            image: "nginx"
`)

	schema := NewInputSchema()
	err := schema.ProcessYAMLInput(yamlInput)
	if err != nil {
		t.Fatalf("Failed to process YAML input: %v", err)
	}

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "input object reference",
			rule: `package test
test { x := input.review.object.kind }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "input array reference",
			rule: `package test
test { x := input.review.object.spec.containers }`,
			varName: "x",
			expected: NewArrayType(NewObjectType(map[string]RegoTypeDef{
				"name":  NewAtomicType(AtomicString),
				"image": NewAtomicType(AtomicString),
			})),
		},
		{
			name: "nested object reference",
			rule: `package test
test { x := input.review.object.metadata }`,
			varName: "x",
			expected: NewObjectType(map[string]RegoTypeDef{
				"name": NewAtomicType(AtomicString),
			}),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			analyzer := AnalyzeTypes(module.Rules[0], schema)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestEqualityBasedInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "equality with literal",
			rule: `package test
test { x = "hello" }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "equality with variable",
			rule: `package test
test { y := 42; x = y }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "equality with array",
			rule: `package test
test { x = [1, 2, 3] }`,
			varName:  "x",
			expected: NewArrayType(NewAtomicType(AtomicInt)),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			analyzer := AnalyzeTypes(module.Rules[0], schema)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestInferType(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	analyzer := NewTypeAnalyzer(schema)

	tests := []struct {
		name     string
		value    ast.Value
		expected RegoTypeDef
	}{
		{
			name:     "nil value",
			value:    nil,
			expected: NewUnknownType(),
		},
		{
			name:     "string value",
			value:    ast.String("test"),
			expected: NewAtomicType(AtomicString),
		},
		{
			name:     "number value",
			value:    ast.Number("42"),
			expected: NewAtomicType(AtomicInt),
		},
		{
			name:     "boolean value",
			value:    ast.Boolean(true),
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name:     "empty array",
			value:    ast.NewArray(),
			expected: NewArrayType(NewUnknownType()),
		},
		{
			name:     "array with strings",
			value:    ast.NewArray(ast.StringTerm("test")),
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name:     "empty object",
			value:    ast.NewObject(),
			expected: NewObjectType(map[string]RegoTypeDef{}),
		},
		{
			name: "array with objects",
			value: ast.NewArray(ast.ObjectTerm([2]*ast.Term{
				ast.StringTerm("key"),
				ast.StringTerm("value"),
			})),
			expected: NewArrayType(NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			})),
		},
		{
			name: "object with string value",
			value: ast.NewObject(
				[2]*ast.Term{
					ast.StringTerm("key"),
					ast.StringTerm("value"),
				},
			),
			expected: NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			}),
		},
		{
			name:     "set value",
			value:    ast.NewSet(),
			expected: NewAtomicType(AtomicSet),
		},
		{
			name:     "variable",
			value:    ast.Var("x"),
			expected: NewUnknownType(),
		},
		{
			name:     "input reference",
			value:    ast.MustParseRef("input.test"),
			expected: NewUnknownType(),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			actual := analyzer.inferType(tt.value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("inferType(%v) = %v, want %v", tt.value, actual, tt.expected)
			}
		})
	}

	// Test caching behavior
	t.Run("caching", func(t *testing.T) {
		t.Parallel()
		val := ast.String("cached")
		expected := NewAtomicType(AtomicString)

		// First call should infer and cache
		first := analyzer.inferType(val)
		if !first.IsEqual(&expected) {
			t.Errorf("First call: got %v, want %v", first, expected)
		}

		// Second call should return cached value
		second := analyzer.inferType(val)
		if !second.IsEqual(&first) {
			t.Errorf("Second call: got %v, want %v (cached value)", second, first)
		}
	})
}

func TestInferExprType(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	analyzer := NewTypeAnalyzer(schema)

	tests := []struct {
		name     string
		rule     string
		expected RegoTypeDef
	}{
		{
			name: "simple term",
			rule: `package test
test { "hello" }`,
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "numeric comparison",
			rule: `package test
test { 1 < 2 }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "string operation",
			rule: `package test
test { contains("hello", "lo") }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "numeric operation",
			rule: `package test
test { plus(1, 2) }`,
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "boolean operation",
			rule: `package test
test { true = false }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "array expression",
			rule: `package test
test { ["a", "b", "c"] }`,
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "object expression",
			rule: `package test
test { {"key": "value"} }`,
			expected: NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			}),
		},
		{
			name: "equality comparison",
			rule: `package test
test { x = y }`,
			expected: NewAtomicType(AtomicBoolean),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			expr := module.Rules[0].Body[0]
			actual := analyzer.InferExprType(expr)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for expression, got %v", tt.expected, actual)
			}
		})
	}
}

func TestInferExprTypeEdgeCases(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	analyzer := NewTypeAnalyzer(schema)

	tests := []struct {
		name     string
		rule     string
		expected RegoTypeDef
	}{
		{
			name: "nil expression",
			rule: `package test
test { true }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "empty array",
			rule: `package test
test { [] }`,
			expected: NewArrayType(NewUnknownType()),
		},
		{
			name: "empty object",
			rule: `package test
test { {} }`,
			expected: NewObjectType(make(map[string]RegoTypeDef)),
		},
		{
			name: "complex nested expression",
			rule: `package test
test { [[1, 2], [3, 4]] }`,
			expected: NewArrayType(NewArrayType(NewAtomicType(AtomicInt))),
		},
		{
			name: "mixed type array",
			rule: `package test
test { [1, "two", true] }`,
			expected: NewArrayType(NewAtomicType(AtomicInt)), // Should infer from first element
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			expr := module.Rules[0].Body[0]
			fmt.Printf("Testing rule: %s %s\n", tt.rule, expr.String())
			actual := analyzer.InferExprType(expr)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for expression, got %v", tt.expected, actual)
			}
		})
	}
}
