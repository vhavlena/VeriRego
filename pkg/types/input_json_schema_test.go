package types

import (
	"testing"
)

func mustSchema(t *testing.T, schema string) *InputJsonSchema {
	t.Helper()
	s := NewInputJsonSchema()
	if err := s.ProcessJSONSchema([]byte(schema)); err != nil {
		t.Fatalf("ProcessJSONSchema error: %v", err)
	}
	return s
}

func TestInputJsonSchema_ObjectBasic(t *testing.T) {
	t.Parallel()
	schema := `{
        "type": "object",
        "properties": {
            "name": {"type": "string"},
            "age": {"type": "integer"},
            "meta": {"type": "object", "properties": {"active": {"type":"boolean"}}}
        }
    }`
	s := mustSchema(t, schema)

	// name: string
	tp, ok := s.GetType(FromGroundPath([]string{"name"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicString {
		t.Fatalf("expected name to be string, got: %v", tp)
	}

	// age: int
	tp, ok = s.GetType(FromGroundPath([]string{"age"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicInt {
		t.Fatalf("expected age to be int, got: %v", tp)
	}

	// meta.active: boolean
	tp, ok = s.GetType(FromGroundPath([]string{"meta", "active"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicBoolean {
		t.Fatalf("expected meta.active to be boolean, got: %v", tp)
	}

	if !s.HasField([]string{"meta", "active"}) {
		t.Fatalf("HasField(meta.active) expected true")
	}

	// Root is object with fields name, age, meta
	root := s.GetTypes()
	if !root.IsObject() {
		t.Fatalf("expected root to be object, got: %v", root)
	}
	if _, ok := root.ObjectFields["name"]; !ok {
		t.Fatalf("expected root to have field 'name'")
	}
	if _, ok := root.ObjectFields["age"]; !ok {
		t.Fatalf("expected root to have field 'age'")
	}
	if _, ok := root.ObjectFields["meta"]; !ok {
		t.Fatalf("expected root to have field 'meta'")
	}
}

func TestInputJsonSchema_ArrayItems(t *testing.T) {
	t.Parallel()
	schema := `{
        "type": "array",
        "items": {"type": "string"}
    }`
	s := mustSchema(t, schema)

	// element type via index path
	tp, ok := s.GetType([]PathNode{{Key: "0", IsGround: true}})
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicString {
		t.Fatalf("expected array element type string, got: %v", tp)
	}
}

func TestInputJsonSchema_AnyOfUnion(t *testing.T) {
	t.Parallel()
	schema := `{
        "anyOf": [
            {"type": "string"},
            {"type": "integer"}
        ]
    }`
	s := mustSchema(t, schema)
	root := s.GetTypes()
	if !root.IsUnion() {
		t.Fatalf("expected union root, got: %v", root)
	}
	// union should contain string and int
	hasStr, hasInt := false, false
	for i := range root.Union {
		u := root.Union[i]
		if u.IsAtomic() && u.AtomicType == AtomicString {
			hasStr = true
		}
		if u.IsAtomic() && u.AtomicType == AtomicInt {
			hasInt = true
		}
	}
	if !(hasStr && hasInt) {
		t.Fatalf("expected union to contain string & int, got: %v", root)
	}
}

func TestInputJsonSchema_TypeArrayUnion(t *testing.T) {
	t.Parallel()
	schema := `{
        "type": ["string", "null"]
    }`
	s := mustSchema(t, schema)
	root := s.GetTypes()
	if !root.IsUnion() {
		t.Fatalf("expected union, got: %v", root)
	}
	hasStr, hasNull := false, false
	for i := range root.Union {
		u := root.Union[i]
		if u.IsAtomic() && u.AtomicType == AtomicString {
			hasStr = true
		}
		if u.IsAtomic() && u.AtomicType == AtomicNull {
			hasNull = true
		}
	}
	if !(hasStr && hasNull) {
		t.Fatalf("expected union to contain string & null, got: %v", root)
	}
}

func TestInputJsonSchema_AllOfMerge(t *testing.T) {
	t.Parallel()
	schema := `{
        "allOf": [
            {"type":"object","properties":{"a":{"type":"string"}}},
            {"type":"object","properties":{"b":{"type":"integer"}}}
        ]
    }`
	s := mustSchema(t, schema)
	root := s.GetTypes()
	if !root.IsObject() {
		t.Fatalf("expected object after allOf merge, got: %v", root)
	}
	a, ok := root.ObjectFields["a"]
	if !ok || !a.IsAtomic() || a.AtomicType != AtomicString {
		t.Fatalf("expected field a:string, got: %v", a)
	}
	b, ok := root.ObjectFields["b"]
	if !ok || !b.IsAtomic() || b.AtomicType != AtomicInt {
		t.Fatalf("expected field b:int, got: %v", b)
	}
}

func TestInputJsonSchema_ItemsTupleUnion(t *testing.T) {
	t.Parallel()
	schema := `{
        "type": "array",
        "items": [
            {"type": "string"},
            {"type": "integer"}
        ]
    }`
	s := mustSchema(t, schema)
	// element type via index path (any index results in union[string|int])
	tp, ok := s.GetType([]PathNode{{Key: "0", IsGround: true}})
	if !ok || tp == nil {
		t.Fatalf("expected element type, got none")
	}
	if !tp.IsUnion() {
		t.Fatalf("expected element union type, got: %v", tp)
	}
	hasStr, hasInt := false, false
	for i := range tp.Union {
		u := tp.Union[i]
		if u.IsAtomic() && u.AtomicType == AtomicString {
			hasStr = true
		}
		if u.IsAtomic() && u.AtomicType == AtomicInt {
			hasInt = true
		}
	}
	if !(hasStr && hasInt) {
		t.Fatalf("expected union element to contain string & int, got: %v", tp)
	}
}

func TestInputJsonSchema_NonGroundObjectPathUnion(t *testing.T) {
	t.Parallel()
	schema := `{
        "type": "object",
        "properties": {
            "a": {"type":"string"},
            "b": {"type":"integer"}
        }
    }`
	s := mustSchema(t, schema)

	// variable object key -> union of all property types
	tp, ok := s.GetType([]PathNode{{Key: "x", IsGround: false}})
	if !ok || tp == nil {
		t.Fatalf("expected type for non-ground path, got none")
	}
	if !tp.IsUnion() {
		t.Fatalf("expected union for non-ground object key, got: %v", tp)
	}
	hasStr, hasInt := false, false
	for i := range tp.Union {
		u := tp.Union[i]
		if u.IsAtomic() && u.AtomicType == AtomicString {
			hasStr = true
		}
		if u.IsAtomic() && u.AtomicType == AtomicInt {
			hasInt = true
		}
	}
	if !(hasStr && hasInt) {
		t.Fatalf("expected union to contain string & int, got: %v", tp)
	}
}
