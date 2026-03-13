package types

import (
	"fmt"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
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
test if { x := "hello" }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "number literal",
			rule: `package test
test if { x := 42 }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "boolean literal",
			rule: `package test
test if { x := true }`,
			varName:  "x",
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "array literal",
			rule: `package test
test if { x := ["a", "b"] }`,
			varName:  "x",
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "object literal",
			rule: `package test
test if { x := {"key": "value"} }`,
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

			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
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
test if { x=true }`,
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

			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
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
test if { x := input.review.object.kind }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "input array reference",
			rule: `package test
test if { x := input.review.object.spec.containers }`,
			varName: "x",
			expected: NewArrayType(NewObjectType(map[string]RegoTypeDef{
				"name":  NewAtomicType(AtomicString),
				"image": NewAtomicType(AtomicString),
			})),
		},
		{
			name: "nested object reference",
			rule: `package test
test if { x := input.review.object.metadata }`,
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

			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)

			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestInputSchemaBasedInferenceComplex(t *testing.T) {
	t.Parallel()

	// Sample YAML input
	yamlInput := []byte("kind: \"Pod\"\n" +
		"metadata:\n" +
		"  name: \"test-pod\"\n" +
		"  image: null\n" +
		"spec:\n" +
		"  containers:\n" +
		"    - name: \"container1\"\n" +
		"      image: \"nginx\"\n")

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
test if { x := input.review.object.metadata[_] }`,
			varName:  "x",
			expected: NewUnionType([]RegoTypeDef{NewAtomicType(AtomicNull), NewAtomicType(AtomicString)}),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
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
test if { x = "hello" }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "equality with variable",
			rule: `package test
test if { y := 42; x = y }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "equality with array",
			rule: `package test
test if { x = [1, 2, 3] }`,
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

			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
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
			schema := NewInputSchema()
			analyzer := NewTypeAnalyzer(schema)
			actual := analyzer.inferAstType(tt.value, nil)
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

		schema := NewInputSchema()
		analyzer := NewTypeAnalyzer(schema)
		// First call should infer and cache
		first := analyzer.inferAstType(val, nil)
		if !first.IsEqual(&expected) {
			t.Errorf("First call: got %v, want %v", first, expected)
		}

		// Second call should return cached value
		second := analyzer.inferAstType(val, nil)
		if !second.IsEqual(&first) {
			t.Errorf("Second call: got %v, want %v (cached value)", second, first)
		}
	})
}

func TestInferExprType(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		rule     string
		expected RegoTypeDef
	}{
		{
			name: "simple term",
			rule: `package test
test if { "hello" }`,
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "numeric comparison",
			rule: `package test
test if { 1 < 2 }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "string operation",
			rule: `package test
test if { contains("hello", "lo") }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "numeric operation",
			rule: `package test
test if { plus(1, 2) }`,
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "boolean operation",
			rule: `package test
test if { true = false }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "array expression",
			rule: `package test
test if { ["a", "b", "c"] }`,
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "object expression",
			rule: `package test
test if { {"key": "value"} }`,
			expected: NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			}),
		},
		{
			name: "equality comparison",
			rule: `package test
test if { x = y }`,
			expected: NewAtomicType(AtomicBoolean),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			schema := NewInputSchema()
			analyzer := NewTypeAnalyzer(schema)

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

	tests := []struct {
		name     string
		rule     string
		expected RegoTypeDef
	}{
		{
			name: "nil expression",
			rule: `package test
test if { true }`,
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "empty array",
			rule: `package test
test if { [] }`,
			expected: NewArrayType(NewUnknownType()),
		},
		{
			name: "empty object",
			rule: `package test
test if { {} }`,
			expected: NewObjectType(make(map[string]RegoTypeDef)),
		},
		{
			name: "complex nested expression",
			rule: `package test
test if { [[1, 2], [3, 4]] }`,
			expected: NewArrayType(NewArrayType(NewAtomicType(AtomicInt))),
		},
		{
			name: "mixed type array",
			rule: `package test
test if { [1, "two", true] }`,
			expected: NewArrayType(NewAtomicType(AtomicInt)), // Should infer from first element
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			schema := NewInputSchema()
			analyzer := NewTypeAnalyzer(schema)

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

// TestParameterSpecInference tests type inference for input.parameters references using a parameter spec
func TestParameterSpecInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	params := Parameters{
		"foo": Parameter{dt: NewAtomicType(AtomicString), name: "foo", required: true},
		"bar": Parameter{dt: NewAtomicType(AtomicInt), name: "bar", required: false},
	}

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "input.parameters string param",
			rule: `package test
test if { x := input.parameters.foo }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "input.parameters int param",
			rule: `package test
test if { x := input.parameters.bar }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}
			analyzer := AnalyzeTypes(module.Rules[0], schema, params)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestRuleHeadTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		rule     string
		ruleName string
		expected RegoTypeDef
	}{
		{
			name: "rule head set type (no value)",
			rule: `package test
my_rule if { true }`,
			ruleName: "my_rule",
			expected: NewAtomicType(AtomicBoolean), // Default for rules with no value is boolean
		},
		{
			name: "rule head with value (string)",
			rule: `package test
my_rule := "foo" if { true }`,
			ruleName: "my_rule",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "rule head with value (array)",
			rule: `package test
my_rule := [1,2,3] if { true }`,
			ruleName: "my_rule",
			expected: NewArrayType(NewAtomicType(AtomicInt)),
		},
		{
			name: "rule head with object value",
			rule: `package test
my_rule := var if { var := {"a": 1, "b": 2} }`,
			ruleName: "my_rule",
			expected: NewObjectType(map[string]RegoTypeDef{
				"a": NewAtomicType(AtomicInt),
				"b": NewAtomicType(AtomicInt),
			}),
		},
		{
			name: "rule head with else branches",
			rule: `package test
my_rule := var if { var := {"a": 1, "b": 2} } else := x if { x := 5 } else := y if { y := "abc" }`,
			ruleName: "my_rule",
			expected: NewUnionType([]RegoTypeDef{
				NewObjectType(map[string]RegoTypeDef{
					"a": NewAtomicType(AtomicInt),
					"b": NewAtomicType(AtomicInt),
				}),
				NewAtomicType(AtomicInt),
				NewAtomicType(AtomicString),
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
			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
			varTerm := ast.VarTerm(tt.ruleName)
			actual := analyzer.GetType(varTerm.Value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for rule %s, got %v", tt.expected, tt.ruleName, actual)
			}
		})
	}
}

func TestDataPackageRuleReferenceTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	// Define a module with a package path and a rule
	ruleSrc := `package mypkg.subpkg
my_rule := {"foo": 1, "bar": "baz"} if { true }`
	module, err := ast.ParseModule("test.rego", ruleSrc)
	if err != nil {
		t.Fatalf("Failed to parse module: %v", err)
	}

	analyzer := AnalyzeTypes(module.Rules[0], schema, nil)

	// The rule head type should be an object with fields foo (int) and bar (string)
	expected := NewObjectType(map[string]RegoTypeDef{
		"foo": NewAtomicType(AtomicInt),
		"bar": NewAtomicType(AtomicString),
	})

	// Build a reference: data.mypkg.subpkg.my_rule
	ref := ast.MustParseRef("data.mypkg.subpkg.my_rule")
	actual := analyzer.inferRefType(ref)

	if !actual.IsEqual(&expected) {
		t.Errorf("Expected type %v for data.mypkg.subpkg.my_rule, got %v", expected, actual)
	}

	// Also test fallback by just rule name (should not match, returns unknown)
	ref2 := ast.MustParseRef("data.my_rule")
	actual2 := analyzer.inferRefType(ref2)
	if !actual2.IsUnknown() {
		t.Errorf("Expected unknown type for data.my_rule, got %v", actual2)
	}
}

func TestDataReferenceObjectInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	// Define a module with a package path and a rule returning an object
	ruleSrc := `package mypkg
my_obj := {"foo": 1, "bar": {"baz": "qux"}} if { true }`
	module, err := ast.ParseModule("test.rego", ruleSrc)
	if err != nil {
		t.Fatalf("Failed to parse module: %v", err)
	}

	analyzer := AnalyzeTypes(module.Rules[0], schema, nil)

	expectedObj := NewObjectType(map[string]RegoTypeDef{
		"foo": NewAtomicType(AtomicInt),
		"bar": NewObjectType(map[string]RegoTypeDef{
			"baz": NewAtomicType(AtomicString),
		}),
	})

	// Test: data.mypkg.my_obj
	ref := ast.MustParseRef("data.mypkg.my_obj")
	actual := analyzer.inferRefType(ref)
	if !actual.IsEqual(&expectedObj) {
		t.Errorf("Expected type %v for data.mypkg.my_obj, got %v", expectedObj, actual)
	}

	// Test: data.mypkg.my_obj.bar
	refBar := ast.MustParseRef("data.mypkg.my_obj.bar")
	actualBar := analyzer.inferRefType(refBar)
	expectedBar := NewObjectType(map[string]RegoTypeDef{
		"baz": NewAtomicType(AtomicString),
	})
	if !actualBar.IsEqual(&expectedBar) {
		t.Errorf("Expected type %v for data.mypkg.my_obj.bar, got %v", expectedBar, actualBar)
	}

	// Test: data.mypkg.my_obj.bar.baz
	refBaz := ast.MustParseRef("data.mypkg.my_obj.bar.baz")
	actualBaz := analyzer.inferRefType(refBaz)
	expectedBaz := NewAtomicType(AtomicString)
	if !actualBaz.IsEqual(&expectedBaz) {
		t.Errorf("Expected type %v for data.mypkg.my_obj.bar.baz, got %v", expectedBaz, actualBaz)
	}

	// Test: data.mypkg.my_obj.unknown (should be unknown)
	refUnknown := ast.MustParseRef("data.mypkg.my_obj.unknown")
	actualUnknown := analyzer.inferRefType(refUnknown)
	if !actualUnknown.IsUnknown() {
		t.Errorf("Expected unknown type for data.mypkg.my_obj.unknown, got %v", actualUnknown)
	}
}

func TestIndexingTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "array indexing",
			rule: `package test
test if { arr := [1,2,3]; x := arr[_] }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "array of strings indexing",
			rule: `package test
test if { arr := ["a", "b"]; x := arr[_] }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "object with mixed value types indexing",
			rule: `package test
test if { obj := {"foo": 1, "bar": "baz"}; x := obj[_] }`,
			varName:  "x",
			expected: NewUnionType([]RegoTypeDef{NewAtomicType(AtomicString), NewAtomicType(AtomicInt)}),
		},
		{
			name: "nested array indexing",
			rule: `package test
test if { arr := [[1,2],[3,4]]; x := arr[_] }`,
			varName:  "x",
			expected: NewArrayType(NewAtomicType(AtomicInt)),
		},
		{
			name: "indexing input array",
			rule: `package test
test if { x := input.review.object.spec.containers[_] }`,
			varName: "x",
			expected: NewObjectType(map[string]RegoTypeDef{
				"name":  NewAtomicType(AtomicString),
				"image": NewAtomicType(AtomicString),
			}),
		},
	}

	// Prepare input schema for the input array test
	yamlInput := []byte(`
      kind: "Pod"
      metadata:
        name: "test-pod"
      spec:
        containers:
          - name: "container1"
            image: "nginx"
`)
	schema.ProcessYAMLInput(yamlInput)

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}
			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestSprintfTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "sprintf assigns string type",
			rule: `package test
test if { sprintf("hello %s", ["world"], x) }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "sprintf with int arg",
			rule: `package test
test if { sprintf("number: %d", [42], x) }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "sprintf with multiple args",
			rule: `package test
test if { sprintf("%s-%d", ["foo", 7], x) }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}
			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}

func TestParametricRuleTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name           string
		module         string
		funcName       string
		expectedReturn RegoTypeDef
		expectedParams []RegoTypeDef
	}{
		{
			name: "predicate with string param constraint",
			module: `package test
is_hello(name) if { name = "hello" }`,
			funcName:       "is_hello",
			expectedReturn: NewAtomicType(AtomicBoolean),
			expectedParams: []RegoTypeDef{NewAtomicType(AtomicString)},
		},
		{
			name: "function with literal return value",
			module: `package test
make_greeting(name) := "Hello, World"`,
			funcName:       "make_greeting",
			expectedReturn: NewAtomicType(AtomicString),
			expectedParams: []RegoTypeDef{NewUnknownType()},
		},
		{
			name: "function returning int via builtin",
			module: `package test
add_one(n) := plus(n, 1)`,
			funcName:       "add_one",
			expectedReturn: NewAtomicType(AtomicInt),
			expectedParams: []RegoTypeDef{NewAtomicType(AtomicInt)},
		},
		{
			name: "predicate with two string param constraints",
			module: `package test
both_strings(a, b) if { a = "x"; b = "y" }`,
			funcName:       "both_strings",
			expectedReturn: NewAtomicType(AtomicBoolean),
			expectedParams: []RegoTypeDef{NewAtomicType(AtomicString), NewAtomicType(AtomicString)},
		},
		{
			name: "predicate with mixed param constraints",
			module: `package test
mixed(s, n) if { s = "hello"; n = 42 }`,
			funcName:       "mixed",
			expectedReturn: NewAtomicType(AtomicBoolean),
			expectedParams: []RegoTypeDef{NewAtomicType(AtomicString), NewAtomicType(AtomicInt)},
		},
		{
			name: "function returning array value",
			module: `package test
make_list(x) := [1, 2, 3]`,
			funcName:       "make_list",
			expectedReturn: NewArrayType(NewAtomicType(AtomicInt)),
			expectedParams: []RegoTypeDef{NewUnknownType()},
		},
		{
			name: "predicate with no param constraints (params remain unknown)",
			module: `package test
always_true(x, y) if { true }`,
			funcName:       "always_true",
			expectedReturn: NewAtomicType(AtomicBoolean),
			expectedParams: []RegoTypeDef{NewUnknownType(), NewUnknownType()},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			mod, err := ast.ParseModule("test.rego", tt.module)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}
			analyzer := NewTypeAnalyzerWithParams(mod.Package.Path, schema, nil)
			analyzer.AnalyzeModule(mod)

			ft, exists := analyzer.Types[tt.funcName]
			if !exists {
				t.Fatalf("Function type for %q not found in type map", tt.funcName)
			}
			if !ft.IsFunction() {
				t.Fatalf("Expected KindFunction for %q, got kind=%v", tt.funcName, ft.Kind)
			}
			if ft.FunctionDef == nil {
				t.Fatalf("FunctionDef is nil for %q", tt.funcName)
			}
			if ft.FunctionDef.Name != tt.funcName {
				t.Errorf("FunctionDef.Name: expected %q, got %q", tt.funcName, ft.FunctionDef.Name)
			}
			if !ft.FunctionDef.ReturnType.IsEqual(&tt.expectedReturn) {
				t.Errorf("ReturnType: expected %v, got %v", tt.expectedReturn.PrettyPrint(), ft.FunctionDef.ReturnType.PrettyPrint())
			}
			if len(ft.FunctionDef.ParamTypes) != len(tt.expectedParams) {
				t.Fatalf("ParamTypes len: expected %d, got %d", len(tt.expectedParams), len(ft.FunctionDef.ParamTypes))
			}
			for i, expected := range tt.expectedParams {
				actual := ft.FunctionDef.ParamTypes[i]
				if !actual.IsEqual(&expected) {
					t.Errorf("ParamTypes[%d]: expected %v, got %v", i, expected.PrettyPrint(), actual.PrettyPrint())
				}
			}
		})
	}
}

func TestUserDefinedFunctionCallTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		module   string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "call to user-defined function returning string",
			module: `package test
make_greeting(prefix) := "Hello, World"
test_rule if { msg := make_greeting("hello") }`,
			varName:  "msg",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "call to user-defined function returning int",
			module: `package test
add_one(n) := plus(n, 1)
test_rule if { result := add_one(5) }`,
			varName:  "result",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "call to user-defined function returning array",
			module: `package test
make_list(x) := [1, 2, 3]
test_rule if { arr := make_list("any") }`,
			varName:  "arr",
			expected: NewArrayType(NewAtomicType(AtomicInt)),
		},
		{
			name: "variable typed via user-defined predicate param constraint propagation",
			module: `package test
is_hello(name) if { name = "hello" }
test_rule if { is_hello(x) }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			mod, err := ast.ParseModule("test.rego", tt.module)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}
			analyzer := NewTypeAnalyzerWithParams(mod.Package.Path, schema, nil)
			analyzer.AnalyzeModule(mod)

			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %q, got %v", tt.expected.PrettyPrint(), tt.varName, actual.PrettyPrint())
			}
		})
	}
}

// compileModule is a test helper that runs OPA's compiler on a parsed module and
// returns the compiled result.  It fails the test if compilation fails.
func compileModule(t *testing.T, mod *ast.Module) *ast.Module {
	t.Helper()
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{mod.Package.Path.String(): mod})
	if compiler.Failed() {
		t.Fatalf("OPA compilation failed: %v", compiler.Errors)
	}
	return compiler.Modules[mod.Package.Path.String()]
}

func TestCompiledModuleFunctionTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name         string
		src          string
		funcName     string
		expectedRet  RegoTypeDef
		expectedPars []RegoTypeDef
	}{
		{
			name: "compiled value-returning function returns int",
			src: `package test
add_one(n) := plus(n, 1)`,
			funcName:     "add_one",
			expectedRet:  NewAtomicType(AtomicInt),
			expectedPars: []RegoTypeDef{NewAtomicType(AtomicInt)},
		},
		{
			name: "compiled predicate function infers string param",
			src: `package test
is_hello(name) if { name = "hello" }`,
			funcName:     "is_hello",
			expectedRet:  NewAtomicType(AtomicBoolean),
			expectedPars: []RegoTypeDef{NewAtomicType(AtomicString)},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			mod, err := ast.ParseModule("test.rego", tt.src)
			if err != nil {
				t.Fatalf("parse error: %v", err)
			}
			compiled := compileModule(t, mod)

			analyzer := NewTypeAnalyzerWithParams(mod.Package.Path, schema, nil)
			analyzer.AnalyzeModule(compiled)

			ft, exists := analyzer.Types[tt.funcName]
			if !exists {
				t.Fatalf("function type %q not found", tt.funcName)
			}
			if !ft.IsFunction() {
				t.Fatalf("expected KindFunction for %q, got %v", tt.funcName, ft.Kind)
			}
			if !ft.FunctionDef.ReturnType.IsEqual(&tt.expectedRet) {
				t.Errorf("ReturnType: want %v, got %v", tt.expectedRet.PrettyPrint(), ft.FunctionDef.ReturnType.PrettyPrint())
			}
			if len(ft.FunctionDef.ParamTypes) != len(tt.expectedPars) {
				t.Fatalf("param count: want %d, got %d", len(tt.expectedPars), len(ft.FunctionDef.ParamTypes))
			}
			for i, want := range tt.expectedPars {
				got := ft.FunctionDef.ParamTypes[i]
				if !got.IsEqual(&want) {
					t.Errorf("ParamTypes[%d]: want %v, got %v", i, want.PrettyPrint(), got.PrettyPrint())
				}
			}
		})
	}
}

func TestCompiledModuleCallSiteTypeInference(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()

	tests := []struct {
		name     string
		src      string
		ruleName string // top-level rule whose inferred type we check
		expected RegoTypeDef
	}{
		{
			name: "rule assigned from compiled value-returning function",
			src: `package test
add_one(n) := plus(n, 1)
my_val := add_one(5)`,
			ruleName: "my_val",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "rule assigned from compiled string-returning function",
			src: `package test
make_greeting(prefix) := "Hello!"
my_msg := make_greeting("World")`,
			ruleName: "my_msg",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "rule assigned from compiled array-returning function",
			src: `package test
make_list(x) := [1, 2, 3]
my_list := make_list("any")`,
			ruleName: "my_list",
			expected: NewArrayType(NewAtomicType(AtomicInt)),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			mod, err := ast.ParseModule("test.rego", tt.src)
			if err != nil {
				t.Fatalf("parse error: %v", err)
			}
			compiled := compileModule(t, mod)

			analyzer := NewTypeAnalyzerWithParams(mod.Package.Path, schema, nil)
			analyzer.AnalyzeModule(compiled)

			actual, exists := analyzer.Types[tt.ruleName]
			if !exists {
				t.Fatalf("type for rule %q not found", tt.ruleName)
			}
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("rule %q: want %v, got %v", tt.ruleName, tt.expected.PrettyPrint(), actual.PrettyPrint())
			}
		})
	}
}

func TestParametricRulePrettyPrint(t *testing.T) {
	t.Parallel()

	ft := NewFunctionType("greet", []RegoTypeDef{NewAtomicType(AtomicString)}, NewAtomicType(AtomicString))
	got := ft.PrettyPrint()
	want := "func greet(string) -> string"
	if got != want {
		t.Errorf("PrettyPrint: expected %q, got %q", want, got)
	}

	ft2 := NewFunctionType("check", []RegoTypeDef{NewAtomicType(AtomicString), NewAtomicType(AtomicInt)}, NewAtomicType(AtomicBoolean))
	got2 := ft2.PrettyPrint()
	want2 := "func check(string, int) -> boolean"
	if got2 != want2 {
		t.Errorf("PrettyPrint: expected %q, got %q", want2, got2)
	}
}

func TestFunctionTypeIsEqual(t *testing.T) {
	t.Parallel()

	f1 := NewFunctionType("f", []RegoTypeDef{NewAtomicType(AtomicString)}, NewAtomicType(AtomicBoolean))
	f2 := NewFunctionType("f", []RegoTypeDef{NewAtomicType(AtomicString)}, NewAtomicType(AtomicBoolean))
	f3 := NewFunctionType("f", []RegoTypeDef{NewAtomicType(AtomicInt)}, NewAtomicType(AtomicBoolean))
	f4 := NewFunctionType("g", []RegoTypeDef{NewAtomicType(AtomicString)}, NewAtomicType(AtomicBoolean))

	if !f1.IsEqual(&f2) {
		t.Error("identical function types should be equal")
	}
	if f1.IsEqual(&f3) {
		t.Error("function types with different param types should not be equal")
	}
	if f1.IsEqual(&f4) {
		t.Error("function types with different names should not be equal")
	}
}

func TestFunctionTypeIsMorePrecise(t *testing.T) {
	t.Parallel()

	// Param goes from unknown to string: more precise
	less := NewFunctionType("f", []RegoTypeDef{NewUnknownType()}, NewAtomicType(AtomicBoolean))
	more := NewFunctionType("f", []RegoTypeDef{NewAtomicType(AtomicString)}, NewAtomicType(AtomicBoolean))
	if !more.IsMorePrecise(&less) {
		t.Error("function with concrete param should be more precise than unknown-param variant")
	}
	if less.IsMorePrecise(&more) {
		t.Error("function with unknown param should not be more precise than concrete-param variant")
	}

	// Function type is more precise than unknown
	unknown := NewUnknownType()
	if !more.IsMorePrecise(&unknown) {
		t.Error("function type should be more precise than unknown")
	}
	if unknown.IsMorePrecise(&more) {
		t.Error("unknown should not be more precise than function type")
	}
}

func TestNestedFunctionCalls(t *testing.T) {
	t.Parallel()
	schema := NewInputSchema()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "sprintf assigns string type",
			rule: `package test
test if { x = concat(concat(u, v),z) }`,
			varName:  "v",
			expected: NewAtomicType(AtomicString),
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", tt.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}
			analyzer := AnalyzeTypes(module.Rules[0], schema, nil)
			varTerm := ast.VarTerm(tt.varName)
			actual := analyzer.GetType(varTerm.Value)
			if !actual.IsEqual(&tt.expected) {
				t.Errorf("Expected type %v for variable %s, got %v", tt.expected, tt.varName, actual)
			}
		})
	}
}
