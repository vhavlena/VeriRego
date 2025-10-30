// Package types provides type analysis for Rego AST.
package types

import (
	"encoding/json"

	qjsonschema "github.com/qri-io/jsonschema"
)

// InputJsonSchema stores type information derived from a JSON Schema document.
// It mirrors the semantics of InputSchema but derives the RegoTypeDef from a JSON Schema
// instead of an example YAML/JSON instance document.
type InputJsonSchema struct {
	types RegoTypeDef
}

// NewInputJsonSchema creates and returns a new InputJsonSchema instance with an empty object type definition.
func NewInputJsonSchema() *InputJsonSchema {
	return &InputJsonSchema{
		types: NewObjectType(make(map[string]RegoTypeDef)),
	}
}

// ProcessJSONSchema parses a JSON Schema (Draft-07-like subset) and stores an internal
// RegoTypeDef approximation. It supports the following schema keywords:
// - type (string or array of strings: "object", "array", "string", "integer"/"number", "boolean", "null")
// - properties (object) for object types
// - items (schema or array of schemas) for array types
// - anyOf / oneOf (array of schemas) -> union of member types
// - allOf (array of schemas) -> merged object/array types where possible; otherwise union approximation
// - enum / const -> union of the value types
// Unsupported or unrecognized keywords are ignored. $ref is not resolved and results in unknown type.
func (s *InputJsonSchema) ProcessJSONSchema(schemaJSON []byte) error {
	// Parse with qri-io/jsonschema to respect JSON Schema structure & keywords
	rs := &qjsonschema.Schema{}
	if err := json.Unmarshal(schemaJSON, rs); err != nil {
		return err
	}
	s.types = s.processQriSchema(rs)
	return nil
}

// ProcessInput implements InputSchemaAPI by delegating to ProcessJSONSchema.
// The input is expected to be a JSON Schema document (Draft-07-like subset).
func (s *InputJsonSchema) ProcessInput(b []byte) error { return s.ProcessJSONSchema(b) }

// GetType returns the RegoTypeDef for a given path in the input schema.
// Semantics match InputSchema.GetType.
func (s *InputJsonSchema) GetType(path []PathNode) (*RegoTypeDef, bool) {
	return s.types.GetTypeFromPath(path)
}

// HasField checks if a field exists at the given path in the input schema.
// Semantics match InputSchema.HasField.
func (s *InputJsonSchema) HasField(path []string) bool {
	typ, ok := s.GetType(FromGroundPath(path))
	return ok && typ != nil
}

// GetTypes returns the complete type definition structure for the input schema.
// Semantics match InputSchema.GetTypes.
func (s *InputJsonSchema) GetTypes() RegoTypeDef {
	return s.types
}

// --------------------------
// JSON Schema processing (qri-io/jsonschema)
// --------------------------

// processQriSchema converts a qri-io/jsonschema Schema into a RegoTypeDef by
// interpreting core JSON Schema keywords (type, properties, items, anyOf, oneOf, allOf).
// Unknown or unsupported shapes are mapped to an unknown type.
func (s *InputJsonSchema) processQriSchema(rs *qjsonschema.Schema) RegoTypeDef {
	if rs == nil {
		return NewUnknownType()
	}

	// First, handle combinators (anyOf/oneOf/allOf)
	if t, ok := s.tryCombinators(rs); ok {
		return t
	}

	// Type can be a string or array of strings. qri exposes a Type keyword struct.
	var typeNames []string
	if v := rs.JSONProp("type"); v != nil {
		switch tv := v.(type) {
		case *qjsonschema.Type:
			typeNames = extractTypeNames(tv)
		case qjsonschema.Type:
			typeNames = extractTypeNames(&tv)
		case string:
			typeNames = []string{tv}
		}
	}

	// If no explicit type, infer from properties/items
	if len(typeNames) == 0 {
		if t, ok := s.objectTypeFromProperties(rs); ok {
			return t
		}
		if t, ok := s.arrayTypeFromItems(rs); ok {
			return t
		}
		// $ref or other unknowns
		return NewUnknownType()
	}

	if len(typeNames) > 1 {
		parts := make([]RegoTypeDef, 0, len(typeNames))
		for _, tn := range typeNames {
			parts = append(parts, s.processByTypeName(rs, tn))
		}
		u := NewUnionType(parts)
		u.CanonizeUnion()
		return u
	}
	return s.processByTypeName(rs, typeNames[0])
}

// extractTypeNames returns the list of JSON Schema type names (e.g. "object",
// "array", "string") from a qri Type, handling both single-string and array
// representations.
func extractTypeNames(t *qjsonschema.Type) []string {
	if t == nil {
		return nil
	}
	// Marshal to inspect if it's a single string or an array of strings
	b, err := t.MarshalJSON()
	if err != nil || len(b) == 0 {
		// Fallback to String()
		s := t.String()
		if s == "" {
			return nil
		}
		return []string{s}
	}
	var single string
	if err := json.Unmarshal(b, &single); err == nil && single != "" {
		return []string{single}
	}
	var arr []string
	if err := json.Unmarshal(b, &arr); err == nil && len(arr) > 0 {
		return arr
	}
	// Unknown shape
	return nil
}

// processByTypeName builds a RegoTypeDef for a specific JSON Schema "type"
// value, delegating to object/array helpers when applicable.
func (s *InputJsonSchema) processByTypeName(rs *qjsonschema.Schema, typ string) RegoTypeDef {
	switch typ {
	case "object":
		if t, ok := s.objectTypeFromProperties(rs); ok {
			return t
		}
		return NewObjectType(map[string]RegoTypeDef{})
	case "array":
		if t, ok := s.arrayTypeFromItems(rs); ok {
			return t
		}
		return NewArrayType(NewUnknownType())
	case "string":
		return NewAtomicType(AtomicString)
	case "integer", "number":
		return NewAtomicType(AtomicInt)
	case "boolean":
		return NewAtomicType(AtomicBoolean)
	case "null":
		return NewAtomicType(AtomicNull)
	default:
		return NewUnknownType()
	}
}

// tryCombinators handles anyOf/oneOf/allOf branches.
func (s *InputJsonSchema) tryCombinators(rs *qjsonschema.Schema) (RegoTypeDef, bool) {
	if v := rs.JSONProp("anyOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			u := s.unionFromSchemas(arr)
			return u, true
		}
	}
	if v := rs.JSONProp("oneOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			u := s.unionFromSchemas(arr)
			return u, true
		}
	}
	if v := rs.JSONProp("allOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			t := s.mergeAllOf(arr)
			return t, true
		}
	}
	return RegoTypeDef{}, false
}

// schemaSliceFromJSONProp converts anyOf/oneOf/allOf JSONProp values to a slice of schemas.
func schemaSliceFromJSONProp(v interface{}) ([]*qjsonschema.Schema, bool) {
	switch s := v.(type) {
	case qjsonschema.AnyOf:
		return []*qjsonschema.Schema(s), true
	case *qjsonschema.AnyOf:
		if s == nil {
			return nil, false
		}
		return []*qjsonschema.Schema(*s), true
	case qjsonschema.OneOf:
		return []*qjsonschema.Schema(s), true
	case *qjsonschema.OneOf:
		if s == nil {
			return nil, false
		}
		return []*qjsonschema.Schema(*s), true
	case qjsonschema.AllOf:
		return []*qjsonschema.Schema(s), true
	case *qjsonschema.AllOf:
		if s == nil {
			return nil, false
		}
		return []*qjsonschema.Schema(*s), true
	default:
		return nil, false
	}
}

// unionFromSchemas converts a slice of qri schemas to their RegoTypeDef union
// and canonizes it to remove duplicates.
func (s *InputJsonSchema) unionFromSchemas(list []*qjsonschema.Schema) RegoTypeDef {
	parts := make([]RegoTypeDef, 0, len(list))
	for _, sub := range list {
		parts = append(parts, s.processQriSchema(sub))
	}
	u := NewUnionType(parts)
	u.CanonizeUnion()
	return u
}

// mergeAllOf merges a list of schemas as in JSON Schema allOf by converting each
// to a RegoTypeDef and combining them with mergeTypes.
func (s *InputJsonSchema) mergeAllOf(list []*qjsonschema.Schema) RegoTypeDef {
	if len(list) == 0 {
		return NewUnknownType()
	}
	acc := s.processQriSchema(list[0])
	for i := 1; i < len(list); i++ {
		acc = mergeTypes(acc, s.processQriSchema(list[i]))
	}
	return acc
}

// objectTypeFromProperties builds an object RegoTypeDef from the "properties"
// keyword if present; returns (type, true) when properties are found.
func (s *InputJsonSchema) objectTypeFromProperties(rs *qjsonschema.Schema) (RegoTypeDef, bool) {
	v := rs.JSONProp("properties")
	if v == nil {
		return RegoTypeDef{}, false
	}
	fields := make(map[string]RegoTypeDef)
	switch props := v.(type) {
	case qjsonschema.Properties:
		for k, child := range props {
			fields[k] = s.processQriSchema(child)
		}
	case *qjsonschema.Properties:
		if props != nil {
			for k, child := range *props {
				fields[k] = s.processQriSchema(child)
			}
		}
	default:
		return RegoTypeDef{}, false
	}
	return NewObjectType(fields), true
}

// arrayTypeFromItems builds an array RegoTypeDef from the "items" keyword if
// present; returns (type, true) when items are found.
func (s *InputJsonSchema) arrayTypeFromItems(rs *qjsonschema.Schema) (RegoTypeDef, bool) {
	v := rs.JSONProp("items")
	if v == nil {
		return RegoTypeDef{}, false
	}
	switch items := v.(type) {
	case *qjsonschema.Items:
		if items == nil {
			return NewArrayType(NewUnknownType()), true
		}
		return arrayTypeFromItemSchemas(s, items.Schemas), true
	case qjsonschema.Items:
		return arrayTypeFromItemSchemas(s, items.Schemas), true
	default:
		return RegoTypeDef{}, false
	}
}

// arrayTypeFromItemSchemas returns an array type whose element type is derived
// from the provided item schemas (unknown for empty, direct type for one,
// union for multiple/tuple-style).
func arrayTypeFromItemSchemas(conv *InputJsonSchema, schemas []*qjsonschema.Schema) RegoTypeDef {
	if len(schemas) == 0 {
		return NewArrayType(NewUnknownType())
	}
	if len(schemas) == 1 {
		et := conv.processQriSchema(schemas[0])
		return NewArrayType(et)
	}
	// tuple-style: union element type
	u := conv.unionFromSchemas(schemas)
	return NewArrayType(u)
}

// mergeTypes attempts to combine two RegoTypeDef values into a single, more precise type.
// Heuristics:
// - If equal, return the type.
// - If one is more precise than the other, return the more precise one.
// - If both are objects, merge their fields (union of field sets, merging recursively).
// - If both are arrays, merge element types recursively.
// - Otherwise, return a union of both and canonize.
func mergeTypes(a, b RegoTypeDef) RegoTypeDef {
	if a.IsEqual(&b) {
		return a
	}
	if a.IsMorePrecise(&b) {
		return a
	}
	if b.IsMorePrecise(&a) {
		return b
	}
	if a.IsObject() && b.IsObject() {
		merged := make(map[string]RegoTypeDef)
		for k, va := range a.ObjectFields {
			if vb, ok := b.ObjectFields[k]; ok {
				merged[k] = mergeTypes(va, vb)
			} else {
				merged[k] = va
			}
		}
		for k, vb := range b.ObjectFields {
			if _, ok := merged[k]; !ok {
				merged[k] = vb
			}
		}
		return NewObjectType(merged)
	}
	if a.IsArray() && b.IsArray() {
		if a.ArrayType == nil || b.ArrayType == nil {
			return NewArrayType(NewUnknownType())
		}
		et := mergeTypes(*a.ArrayType, *b.ArrayType)
		return NewArrayType(et)
	}
	u := NewUnionType([]RegoTypeDef{a, b})
	u.CanonizeUnion()
	return u
}
