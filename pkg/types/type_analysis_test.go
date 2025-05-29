package types

import (
	"testing"

	"github.com/open-policy-agent/opa/ast"
)

// compareAtomicTypes compares two atomic types
func compareAtomicTypes(type1, type2 RegoTypeDef) bool {
	return type1.AtomicType == type2.AtomicType
}

// compareArrayTypes compares two array types recursively
func compareArrayTypes(type1, type2 RegoTypeDef) bool {
	if type1.ArrayType == nil || type2.ArrayType == nil {
		return type1.ArrayType == type2.ArrayType
	}
	return compareTypes(*type1.ArrayType, *type2.ArrayType)
}

// compareObjectTypes compares two object types recursively
func compareObjectTypes(type1, type2 RegoTypeDef) bool {
	if len(type1.ObjectFields) != len(type2.ObjectFields) {
		return false
	}
	for key, val1 := range type1.ObjectFields {
		val2, exists := type2.ObjectFields[key]
		if !exists || !compareTypes(val1, val2) {
			return false
		}
	}
	return true
}

// compareTypes compares two RegoTypeDef values for equality
func compareTypes(type1, type2 RegoTypeDef) bool {
	if type1.Kind != type2.Kind {
		return false
	}

	switch type1.Kind {
	case KindAtomic:
		return compareAtomicTypes(type1, type2)
	case KindArray:
		return compareArrayTypes(type1, type2)
	case KindObject:
		return compareObjectTypes(type1, type2)
	case KindUnknown:
		return true
	default:
		return false
	}
}

func TestBasicTypeInference(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name     string
		rule     string
		varName  string
		expected RegoTypeDef
	}{
		{
			name: "string assignment",
			rule: `package test
test { x := "hello" }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "string equality",
			rule: `package test
test { x = "hello" }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "number assignment",
			rule: `package test
test { x := 42 }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "boolean assignment",
			rule: `package test
test { x := true }`,
			varName:  "x",
			expected: NewAtomicType(AtomicBoolean),
		},
		{
			name: "array assignment",
			rule: `package test
test { x := ["a", "b"] }`,
			varName:  "x",
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "object assignment",
			rule: `package test
test { x := {"key": "value"} }`,
			varName: "x",
			expected: NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			}),
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
			actual := visitor.GetTypes()[ttinst.varName]
			if actual.Kind != ttinst.expected.Kind ||
				(actual.IsAtomic() && actual.AtomicType != ttinst.expected.AtomicType) {
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
		expected RegoTypeDef
	}{
		{
			name: "input array reference",
			rule: `package test
test { x := input.roles }`,
			varName:  "x",
			expected: NewObjectType(make(map[string]RegoTypeDef)),
		},
		{
			name: "input object reference",
			rule: `package test
test { x := input.parameters }`,
			varName:  "x",
			expected: NewObjectType(make(map[string]RegoTypeDef)),
		},
		{
			name: "array index variable",
			rule: `package test
test { arr := [1, 2, 3]; x := arr[i] }`,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "array index variable 2",
			rule: `package test
test { arr := [1, 2, 3]; x := arr[i]; y := arr[j]; i < j }`,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "nested object reference",
			rule: `package test
test { x := input.parameters.user.profile }`,
			varName:  "x",
			expected: NewObjectType(make(map[string]RegoTypeDef)),
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
			actual := visitor.GetTypes()[ttinst.varName]
			if actual.Kind != ttinst.expected.Kind ||
				(actual.IsAtomic() && actual.AtomicType != ttinst.expected.AtomicType) {
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
		expected RegoTypeDef
	}{
		{
			name: "string function arg",
			rule: `package test
test { contains(x, "substring") }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "numeric function arg",
			rule: `package test
test { plus(x, 5) }`,
			varName:  "x",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "boolean function arg",
			rule: `package test
test { equal(x, true) }`,
			varName:  "x",
			expected: NewAtomicType(AtomicBoolean),
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
			actual := visitor.GetTypes()[ttinst.varName]
			if actual.Kind != ttinst.expected.Kind ||
				(actual.IsAtomic() && actual.AtomicType != ttinst.expected.AtomicType) {
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
		expected RegoTypeDef
	}{
		{
			name: "array comprehension",
			rule: `package test
import future.keywords.in
test { x := [i | some i in input.roles] }`,
			varName:  "x",
			expected: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "set comprehension",
			rule: `package test
import future.keywords.in
test { x := {i | some i in input.roles} }`,
			varName:  "x",
			expected: NewAtomicType(AtomicSet),
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
			actual := visitor.GetTypes()[ttinst.varName]
			if !compareTypes(actual, ttinst.expected) {
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
		expected RegoTypeDef
	}{
		{
			name: "input string reference array",
			rule: `package test
		test { x := y.test[i] }`,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "input string equality array",
			rule: `package test
		test { x = input.test[i] }`,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "input string reference array with int index",
			rule: `package test
		test { i = 5; x := input.test[i] }`,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "else branch",
			rule: `package test
		test { true } else = "default" { i = 5 } `,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
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
			actual := visitor.GetTypes()[ttinst.varName]
			if !compareTypes(actual, ttinst.expected) {
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
		expected RegoTypeDef
	}{
		{
			name: "input object reference with yaml schema",
			rule: `package test
test { x := input.review.object.kind }`,
			varName:  "x",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "nested array reference",
			rule: `package test
test { x := input.review.object.spec.containers }`,
			varName:  "x",
			expected: NewArrayType(NewObjectType(make(map[string]RegoTypeDef))),
		},
		{
			name: "array index reference",
			rule: `package test
test { x := input.review.object.spec.containers[i] }`,
			varName:  "i",
			expected: NewAtomicType(AtomicInt),
		},
		{
			name: "nested object reference",
			rule: `package test
test { x := input.review.object.metadata.labels }`,
			varName:  "x",
			expected: NewObjectType(make(map[string]RegoTypeDef)),
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

			actual := visitor.GetTypes()[ttinst.varName]
			if !compareTypes(actual, ttinst.expected) {
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
		expected RegoTypeDef
	}{
		{
			name: "input object reference with yaml schema",
			rule: `package test
test { x := input.review.object.metadata; y := x.name }`,
			varName:  "y",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "rules types",
			rule: `package test
test { x := input.review.object.metadata; y := z.name }
node_status = z { z = input.review.object.metadata.name }`,
			varName:  "node_status",
			expected: NewAtomicType(AtomicString),
		},
		{
			name: "rule with object propagation",
			rule: `package test
test := x { x := input.review.object }
rule { y := test.kind }`,
			varName:  "y",
			expected: NewAtomicType(AtomicString),
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
				actual := visitor.GetRuleTypes()[ttinst.varName]
				if !compareTypes(actual, ttinst.expected) {
					t.Errorf("Expected type %v for variable %s, got %v", ttinst.expected, ttinst.varName, actual)
				}
			} else {
				actual := visitor.GetTypes()[ttinst.varName]
				if !compareTypes(actual, ttinst.expected) {
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
		expectedType RegoTypeDef
	}{
		{
			name: "direct string value",
			rule: `package test
test = "hello" { true }`,
			ruleName:     "test",
			expectedType: NewAtomicType(AtomicString),
		},
		{
			name: "direct number value",
			rule: `package test
test = 42 { true }`,
			ruleName:     "test",
			expectedType: NewAtomicType(AtomicInt),
		},
		{
			name: "array value",
			rule: `package test
test = ["a", "b"] { true }`,
			ruleName:     "test",
			expectedType: NewArrayType(NewAtomicType(AtomicString)),
		},
		{
			name: "object value",
			rule: `package test
test = {"key": "value"} { true }`,
			ruleName: "test",
			expectedType: NewObjectType(map[string]RegoTypeDef{
				"key": NewAtomicType(AtomicString),
			}),
		},
		{
			name: "reference value",
			rule: `package test
test = input.review.object.metadata.name { true }`,
			ruleName:     "test",
			expectedType: NewAtomicType(AtomicString),
		},
		{
			name: "complex rule with assignment",
			rule: `package test
complex_rule = result {
    result := input.review.object.kind
}`,
			ruleName:     "complex_rule",
			expectedType: NewAtomicType(AtomicString),
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
			expectedType: NewAtomicType(AtomicString),
		},
		{
			name: "rule with array reference",
			rule: `package test
containers = val {
    val := input.review.object.spec.containers
}`,
			ruleName:     "containers",
			expectedType: NewArrayType(NewObjectType(make(map[string]RegoTypeDef))),
		},
		{
			name: "rule with boolean result",
			rule: `package test
is_nginx = res {
    input.review.object.spec.containers[_].image == "nginx"
    res := true
}`,
			ruleName:     "is_nginx",
			expectedType: NewAtomicType(AtomicBoolean),
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

			actual := visitor.GetRuleTypes()[ttinst.ruleName]
			if !compareTypes(actual, ttinst.expectedType) {
				t.Errorf("Expected type %v for rule %s, got %v", ttinst.expectedType, ttinst.ruleName, actual)
			}
		})
	}
}
