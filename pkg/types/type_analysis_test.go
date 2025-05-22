package types

import (
	"testing"

	"github.com/open-policy-agent/opa/ast"
)

func TestBasicTypeInference(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "string assignment",
			rule: `package test
test { x := "hello" }`,
			varName:  "x",
			expected: TypeString,
		},
		{
			name: "string equality",
			rule: `package test
test { x = "hello" }`,
			varName:  "x",
			expected: TypeString,
		},
		{
			name: "number assignment",
			rule: `package test
test { x := 42 }`,
			varName:  "x",
			expected: TypeInt,
		},
		{
			name: "boolean assignment",
			rule: `package test
test { x := true }`,
			varName:  "x",
			expected: TypeBoolean,
		},
		{
			name: "array assignment",
			rule: `package test
test { x := ["a", "b"] }`,
			varName:  "x",
			expected: TypeArray,
		},
		{
			name: "object assignment",
			rule: `package test
test { x := {"key": "value"} }`,
			varName:  "x",
			expected: TypeObject,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			types := AnalyzeTypes(module.Rules[0])
			if actual := types[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}

func TestReferenceTypeInference(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "input array reference",
			rule: `package test
test { x := input.roles }`,
			varName:  "x",
			expected: TypeObject,
		},
		{
			name: "input object reference",
			rule: `package test
test { x := input.parameters }`,
			varName:  "x",
			expected: TypeObject,
		},
		{
			name: "input string reference",
			rule: `package test
test { x := input.test }`,
			varName:  "x",
			expected: TypeObject,
		},
		{
			name: "input string reference array",
			rule: `package test
test { x := input.test[i] }`,
			varName:  "i",
			expected: TypeIndex,
		},
		{
			name: "array index variable 2",
			rule: `package test
test { arr := [1, 2, 3]; x := arr[i]; y := arr[j]; i < j }`,
			varName:  "i",
			expected: TypeInt,
		},
		{
			name: "nested object reference",
			rule: `package test
test { x := input.parameters.user.profile }`,
			varName:  "x",
			expected: TypeObject,
		},
		{
			name: "array reference with numeric index",
			rule: `package test
test { x := input.roles[0] }`,
			varName:  "x",
			expected: TypeObject,
		},
		{
			name: "input reference itself",
			rule: `package test
test { x := input }`,
			varName:  "x",
			expected: TypeObject,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			types := AnalyzeTypes(module.Rules[0])
			if actual := types[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}

func TestBuiltinFunctionTypeInference(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "string function arg",
			rule: `package test
test { contains(x, "substring") }`,
			varName:  "x",
			expected: TypeString,
		},
		{
			name: "numeric function arg",
			rule: `package test
test { plus(x, 5) }`,
			varName:  "x",
			expected: TypeInt,
		},
		{
			name: "boolean function arg",
			rule: `package test
test { equal(x, true) }`,
			varName:  "x",
			expected: TypeBoolean,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			types := AnalyzeTypes(module.Rules[0])
			if actual := types[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}

func TestComprehensionTypeInference(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "array comprehension",
			rule: `package test
import future.keywords.in
test { x := [i | some i in input.roles] }`,
			varName:  "x",
			expected: TypeArray,
		},
		{
			name: "set comprehension",
			rule: `package test
import future.keywords.in
test { x := {i | some i in input.roles} }`,
			varName:  "x",
			expected: TypeSet,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			types := AnalyzeTypes(module.Rules[0])
			if actual := types[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}

func TestReferenceTypeInference2(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "input string reference array",
			rule: `package test
		test { x := input.test[i] }`,
			varName:  "i",
			expected: TypeIndex,
		},
		{
			name: "input string reference array with int index",
			rule: `package test
		test { i = 5; x := input.test[i] }`,
			varName:  "i",
			expected: TypeInt,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			types := AnalyzeTypes(module.Rules[0])
			if actual := types[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}
