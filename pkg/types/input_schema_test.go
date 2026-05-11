package types

import (
	"testing"
)

func TestInputSchema_ProcessNode_MixedArray(t *testing.T) {
	yamlData := []byte(`
user:
  data: 
    - 42
    - "forty-two"
`)
	schema := NewInputSchema()
	if err := schema.ProcessYAMLInput(yamlData); err != nil {
		t.Fatalf("failed to process YAML: %v", err)
	}

	// Request type of the first element "user.data[0]"
	path := FromGroundPath([]string{"user", "data", "0"})
	typ, exists := schema.GetType(path)

	if !exists || typ == nil {
		t.Fatalf("expected to resolve type for user.data[0]")
	}

	if !typ.IsUnion() {
		t.Fatalf("expected user.data to be an array of UNION types, got %s", typ.Kind)
	}

	// Verify that the union contains both string and int
	hasInt := false
	hasString := false

	for _, u := range typ.Union {
		if u.IsAtomic() && u.AtomicType == AtomicInt {
			hasInt = true
		}
		if u.IsAtomic() && u.AtomicType == AtomicString {
			hasString = true
		}
	}

	if !hasInt || !hasString {
		t.Fatalf("Union type did not contain both int and string! Contained: %v", typ.Union)
	}
}

func TestInputSchema_ProcessNode_HomogeneousArray(t *testing.T) {
	yamlData := []byte(`
user:
  data: [67, 68, 69, 70]
`)

	schema := NewInputSchema()
	if err := schema.ProcessYAMLInput(yamlData); err != nil {
		t.Fatalf("failed to process YAML: %v", err)
	}

	// Request type of the first element "user.data[0]"
	path := FromGroundPath([]string{"user", "data", "0"})
	typ, exists := schema.GetType(path)

	if !exists || typ == nil {
		t.Fatalf("expected to resolve type for user.data[0]")
	}

	// Should collapse directly into atomic int via CanonizeUnion
	if typ.IsUnion() {
		t.Fatalf("expected homogeneous array elements to canonize into an atomic type instead of remaining a union")
	}

	if !typ.IsAtomic() || typ.AtomicType != AtomicInt {
		t.Fatalf("expected homogeneous array elements to resolve precisely to 'int'")
	}
}
