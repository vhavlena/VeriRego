package types

import (
	"encoding/json"
	"testing"

	qjsonschema "github.com/qri-io/jsonschema"
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

func TestInputJsonSchema_AdditionalProperties_True(t *testing.T) {
	t.Parallel()
	schema := `{
		"type": "object",
		"properties": {"known": {"type":"boolean"}},
		"additionalProperties": true
	}`
	s := mustSchema(t, schema)

	// path leading to additionalProperties: root ""
	if _, ok := s.additionalPaths[""]; !ok {
		t.Fatalf("expected additionalProperties recorded at root path")
	}
	if ap, ok := s.additionalDefs[""]; !ok || !ap.IsUnknown() {
		t.Fatalf("expected root additionalProperties type to be unknown, got: %v", ap)
	}

	// known is boolean
	tp, ok := s.GetType(FromGroundPath([]string{"known"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicBoolean {
		t.Fatalf("expected known:boolean, got: %v", tp)
	}
	// unknown field should be allowed with Unknown type
	tp, ok = s.GetType(FromGroundPath([]string{"anything"}))
	if !ok || tp == nil || !tp.IsUnknown() {
		t.Fatalf("expected additional unknown type for 'anything', got: %v", tp)
	}
	if !s.HasField([]string{"anything"}) {
		t.Fatalf("HasField for additionalProperties:true should be true for unknown field")
	}
}

func TestInputJsonSchema_AdditionalProperties_SchemaString(t *testing.T) {
	t.Parallel()
	schema := `{
		"type": "object",
		"additionalProperties": {"type":"string"}
	}`
	s := mustSchema(t, schema)

	// path leading to additionalProperties: root ""
	if _, ok := s.additionalPaths[""]; !ok {
		t.Fatalf("expected additionalProperties recorded at root path")
	}
	if ap, ok := s.additionalDefs[""]; !ok || !ap.IsAtomic() || ap.AtomicType != AtomicString {
		t.Fatalf("expected root additionalProperties type to be string, got: %v", ap)
	}

	tp, ok := s.GetType(FromGroundPath([]string{"dyn"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicString {
		t.Fatalf("expected additionalProperties schema to give string, got: %v", tp)
	}

	// Nested object additionalProperties schema
	schema2 := `{
		"type": "object",
		"additionalProperties": {
			"type":"object",
			"properties": {"age": {"type":"integer"}},
			"additionalProperties": {"type":"string"}
		}
	}`
	s2 := mustSchema(t, schema2)
	// root has AP object type recorded at path ""
	if _, ok := s2.additionalPaths[""]; !ok {
		t.Fatalf("expected additionalProperties recorded at root for nested object schema")
	}
	if apRoot, ok := s2.additionalDefs[""]; !ok || !apRoot.IsObject() {
		t.Fatalf("expected root additionalProperties type to be object, got: %v", apRoot)
	} else {
		age, ok := apRoot.ObjectFields["age"]
		if !ok || !age.IsAtomic() || age.AtomicType != AtomicInt {
			t.Fatalf("expected nested AP object to have age:int, got: %v", age)
		}
	}
	// nested additionalProperties recorded at path "*" with string type
	if _, ok := s2.additionalPaths["*"]; !ok {
		t.Fatalf("expected nested additionalProperties recorded at path '*'")
	}
	if apNested, ok := s2.additionalDefs["*"]; !ok || !apNested.IsAtomic() || apNested.AtomicType != AtomicString {
		t.Fatalf("expected nested additionalProperties type string at '*', got: %v", apNested)
	}
	// unknown top-level key yields object
	tp, ok = s2.GetType(FromGroundPath([]string{"user"}))
	if !ok || tp == nil || !tp.IsObject() {
		t.Fatalf("expected additional property object at user, got: %v", tp)
	}
	// user.age is integer
	tp, ok = s2.GetType(FromGroundPath([]string{"user", "age"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicInt {
		t.Fatalf("expected user.age:int, got: %v", tp)
	}
	// user.anyOther is string (from user's own additionalProperties)
	tp, ok = s2.GetType(FromGroundPath([]string{"user", "nickname"}))
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicString {
		t.Fatalf("expected user.nickname:string, got: %v", tp)
	}
}

func TestInputJsonSchema_AdditionalProperties_VarKey(t *testing.T) {
	t.Parallel()
	schema := `{
		"type": "object",
		"additionalProperties": {"type":"integer"}
	}`
	s := mustSchema(t, schema)
	// root AP integer at path ""
	if ap, ok := s.additionalDefs[""]; !ok || !ap.IsAtomic() || ap.AtomicType != AtomicInt {
		t.Fatalf("expected root additionalProperties type to be integer, got: %v", ap)
	}
	tp, ok := s.GetType([]PathNode{{Key: "x", IsGround: false}})
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicInt {
		t.Fatalf("expected var key to resolve to additionalProperties integer, got: %v", tp)
	}
}

func TestInputJsonSchema_AdditionalProperties_CombinatorsMerge(t *testing.T) {
	t.Parallel()
	schema := `{
		"anyOf": [
			{"type": "object", "additionalProperties": {"type":"string"}},
			{"type": "object", "additionalProperties": {"type":"integer"}}
		]
	}`
	s := mustSchema(t, schema)
	// root AP should be union[string|int]
	if ap, ok := s.additionalDefs[""]; !ok || !ap.IsUnion() {
		t.Fatalf("expected root additionalProperties union, got: %v", ap)
	} else {
		hasStr, hasInt := false, false
		for i := range ap.Union {
			u := ap.Union[i]
			if u.IsAtomic() && u.AtomicType == AtomicString {
				hasStr = true
			}
			if u.IsAtomic() && u.AtomicType == AtomicInt {
				hasInt = true
			}
		}
		if !(hasStr && hasInt) {
			t.Fatalf("expected union to contain string & int for additionalProperties, got: %v", ap)
		}
	}
	tp, ok := s.GetType(FromGroundPath([]string{"dyn"}))
	if !ok || tp == nil || !tp.IsUnion() {
		t.Fatalf("expected union for additionalProperties merged from anyOf, got: %v", tp)
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
		t.Fatalf("expected union to contain string & int for additionalProperties, got: %v", tp)
	}
}

func TestInputJsonSchema_AdditionalProperties_InArrayItems(t *testing.T) {
	t.Parallel()
	schema := `{
		"type": "array",
		"items": {"type":"object", "additionalProperties": {"type":"string"}}
	}`
	s := mustSchema(t, schema)
	// path leading to additionalProperties inside array elements: "[]"
	if ap, ok := s.additionalDefs["[]"]; !ok || !ap.IsAtomic() || ap.AtomicType != AtomicString {
		t.Fatalf("expected additionalProperties type string at array element path '[]', got: %v", ap)
	}
	// element object unknown field type
	tp, ok := s.GetType([]PathNode{{Key: "0", IsGround: true}, {Key: "foo", IsGround: true}})
	if !ok || tp == nil || !tp.IsAtomic() || tp.AtomicType != AtomicString {
		t.Fatalf("expected array element object additional property type string, got: %v", tp)
	}
}

// Debug helper to inspect qri additionalProperties representation when tests fail.
func TestDebug_AdditionalProperties_Type(t *testing.T) {
	schema := `{
		"type": "object",
		"additionalProperties": {"type":"string"}
	}`
	rs := &qjsonschema.Schema{}
	if err := json.Unmarshal([]byte(schema), rs); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	v := rs.JSONProp("additionalProperties")
	t.Logf("additionalProperties JSONProp type: %T", v)
}

func TestDebug_AdditionalProperties_Recorded(t *testing.T) {
	s := mustSchema(t, `{
		"type":"object",
		"additionalProperties": {"type":"string"}
	}`)
	if _, ok := s.additionalPaths[""]; !ok {
		t.Fatalf("expected additionalProperties recorded at root path")
	}
}

func TestDebug_MaybeRecordAP(t *testing.T) {
	schema := `{
		"type": "object",
		"additionalProperties": {"type":"string"}
	}`
	rs := &qjsonschema.Schema{}
	if err := json.Unmarshal([]byte(schema), rs); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	s := NewInputJsonSchema()
	s.maybeRecordAdditionalProperties(rs, nil)
	if _, ok := s.additionalPaths[""]; !ok {
		t.Fatalf("expected additionalProperties recorded at root path by maybeRecordAdditionalProperties")
	}
}

func TestDebug_ProcessQriSchemaAt_Records(t *testing.T) {
	schema := `{
		"type": "object",
		"additionalProperties": {"type":"string"}
	}`
	rs := &qjsonschema.Schema{}
	if err := json.Unmarshal([]byte(schema), rs); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	s := NewInputJsonSchema()
	_ = s.processQriSchemaAt(rs, nil)
	if _, ok := s.additionalPaths[""]; !ok {
		t.Fatalf("expected processQriSchemaAt to record additionalProperties at root path")
	}
}
