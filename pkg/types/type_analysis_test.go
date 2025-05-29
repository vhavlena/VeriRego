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

			visitor := AnalyzeTypes(module.Rules[0])
			if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
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

			visitor := AnalyzeTypes(module.Rules[0])
			if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
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

			visitor := AnalyzeTypes(module.Rules[0])
			if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
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

			visitor := AnalyzeTypes(module.Rules[0])
			if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
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
		test { x := y.test[i] }`,
			varName:  "i",
			expected: TypeIndex,
		},
		{
			name: "input string equality array",
			rule: `package test
		test { x = input.test[i] }`,
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
		{
			name: "else branch",
			rule: `package test
		test { true } else = "default" { i = 5 } `,
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

			visitor := AnalyzeTypes(module.Rules[0])
			if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}

func TestYAMLBasedTypeInference(t *testing.T) {
	t.Parallel()

	// Sample YAML input
	yamlInput := []byte(`
input:
  review:
    object:
      kind: "Pod"
      metadata:
        name: "test-pod"
        labels:
          app: "myapp"
      spec:
        containers:
          - name: "container1"
            image: "nginx"
            ports:
              - containerPort: 80
`)

	visitor := NewTypeVisitor()
	err := visitor.GetTypeInfo().InputSchema.ProcessYAMLInput(yamlInput)
	if err != nil {
		t.Fatalf("Failed to process YAML input: %v", err)
	}

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "input object reference with yaml schema",
			rule: `package test
test { x := input.review.object.kind }`,
			varName:  "x",
			expected: TypeString,
		},
		{
			name: "nested array reference",
			rule: `package test
test { x := input.review.object.spec.containers }`,
			varName:  "x",
			expected: TypeArray,
		},
		{
			name: "array index reference",
			rule: `package test
test { x := input.review.object.spec.containers[i] }`,
			varName:  "i",
			expected: TypeIndex,
		},
		{
			name: "nested object reference",
			rule: `package test
test { x := input.review.object.metadata.labels }`,
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

			visitor := NewTypeVisitor()
			err = visitor.GetTypeInfo().InputSchema.ProcessYAMLInput(yamlInput)
			if err != nil {
				t.Fatalf("Failed to process YAML input: %v", err)
			}

			for _, expr := range module.Rules[0].Body {
				visitor.VisitExpr(expr)
			}

			if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
				t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
			}
		})
	}
}

func TestYAMLBasedPropagation(t *testing.T) {
	t.Parallel()

	// Sample YAML input
	yamlInput := []byte(`
input:
  review:
    object:
      kind: "Pod"
      metadata:
        name: "test-pod"
        labels:
          app: "myapp"
      spec:
        containers:
          - name: "container1"
            image: "nginx"
            ports:
              - containerPort: 80
`)

	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoType
	}{
		{
			name: "input object reference with yaml schema",
			rule: `package test
test { x := input.review.object.metadata; y := x.name }`,
			varName:  "y",
			expected: TypeString,
		},
		{
			name: "rules types",
			rule: `package test
test { x := input.review.object.metadata; y := z.name }
node_status = z { z = input.review.object.metadata.name }`,
			varName:  "node_status",
			expected: TypeString,
		},
		{
			name: "rule with object propagation",
			rule: `package test
test := x { x := input.review.object }
rule { y := test.kind }`,
			varName:  "y",
			expected: TypeString,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			visitor := NewTypeVisitor()
			err = visitor.GetTypeInfo().InputSchema.ProcessYAMLInput(yamlInput)
			if err != nil {
				t.Fatalf("Failed to process YAML input: %v", err)
			}

			// For each rule in the module, analyze it with the same visitor
			for _, rule := range module.Rules {
				visitor = visitor.VisitRule(rule)
			}

			if ttinst.name == "rules types" {
				if actual := visitor.GetRuleTypes()[ttinst.varName]; actual != ttinst.expected {
					t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
				}
			} else {
				if actual := visitor.GetTypes()[ttinst.varName]; actual != ttinst.expected {
					t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
				}
			}
		})
	}
}

func TestRuleTypeInference(t *testing.T) {
	t.Parallel()

	// Sample YAML input for reference type testing
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
            ports:
              - containerPort: 80
`)

	tests := []struct {
		name         string
		rule         string
		ruleName     string
		expectedType RegoType
	}{
		{
			name: "direct string value",
			rule: `package test
test = "hello" { true }`,
			ruleName:     "test",
			expectedType: TypeString,
		},
		{
			name: "direct number value",
			rule: `package test
test = 42 { true }`,
			ruleName:     "test",
			expectedType: TypeInt,
		},
		{
			name: "array value",
			rule: `package test
test = ["a", "b"] { true }`,
			ruleName:     "test",
			expectedType: TypeArray,
		},
		{
			name: "object value",
			rule: `package test
test = {"key": "value"} { true }`,
			ruleName:     "test",
			expectedType: TypeObject,
		},
		{
			name: "reference value",
			rule: `package test
test = input.review.object.metadata.name { true }`,
			ruleName:     "test",
			expectedType: TypeString,
		},
		{
			name: "complex rule with assignment",
			rule: `package test
complex_rule = result {
    result := input.review.object.kind
}`,
			ruleName:     "complex_rule",
			expectedType: TypeString,
		},
		{
			name: "rule with else branch",
			rule: `package test
test = "value1" {
    true
} else = "value2" {
    false
}`,
			ruleName:     "test",
			expectedType: TypeString,
		},
		{
			name: "rule with array reference",
			rule: `package test
containers = val {
    val := input.review.object.spec.containers
}`,
			ruleName:     "containers",
			expectedType: TypeArray,
		},
		{
			name: "rule with boolean result",
			rule: `package test
is_nginx = res {
    input.review.object.spec.containers[_].image == "nginx"
    res := true
}`,
			ruleName:     "is_nginx",
			expectedType: TypeBoolean,
		},
	}

	for _, ttinst := range tests {
		t.Run(ttinst.name, func(t *testing.T) {
			t.Parallel()
			module, err := ast.ParseModule("test.rego", ttinst.rule)
			if err != nil {
				t.Fatalf("Failed to parse module: %v", err)
			}

			visitor := NewTypeVisitor()
			err = visitor.GetTypeInfo().InputSchema.ProcessYAMLInput(yamlInput)
			if err != nil {
				t.Fatalf("Failed to process YAML input: %v", err)
			}

			for _, rule := range module.Rules {
				visitor = visitor.VisitRule(rule)
			}

			if actual := visitor.GetRuleTypes()[ttinst.ruleName]; actual != ttinst.expectedType {
				t.Errorf("Expected type %v for rule %s, got %v", ttinst.expectedType, ttinst.ruleName, actual)
			}
		})
	}
}
