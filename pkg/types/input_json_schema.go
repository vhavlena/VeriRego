// Package types provides type analysis for Rego AST.
package types

import (
	"encoding/json"
	"strings"

	jptr "github.com/qri-io/jsonpointer"
	qjsonschema "github.com/qri-io/jsonschema"
)

// InputJsonSchema stores type information derived from a JSON Schema document.
// It mirrors the semantics of InputSchema but derives the RegoTypeDef from a JSON Schema
// instead of an example YAML/JSON instance document.
type InputJsonSchema struct {
	types RegoTypeDef
	// additionalDefs maps an object path key to the type allowed for additionalProperties at that path.
	// The path key is a '/'-joined sequence of segments where array elements are represented by "[]".
	additionalDefs map[string]RegoTypeDef
	// additionalPaths is a set of paths where additionalProperties is explicitly allowed (true or schema).
	additionalPaths map[string]struct{}
}

// NewInputJsonSchema creates and returns a new InputJsonSchema instance with an empty object type definition.
//
// Returns:
//
//	*InputJsonSchema: A new instance with an empty object type definition.
func NewInputJsonSchema() *InputJsonSchema {
	return &InputJsonSchema{
		types:           NewObjectType(make(map[string]RegoTypeDef)),
		additionalDefs:  make(map[string]RegoTypeDef),
		additionalPaths: make(map[string]struct{}),
	}
}

// ProcessJSONSchema parses a JSON Schema (Draft-07-like subset) and stores an internal
// RegoTypeDef approximation.
//
// Supported keywords include (non-exhaustive):
//   - type (string or array of strings: "object", "array", "string", "integer"/"number", "boolean", "null")
//   - properties (object) for object types
//   - items (schema or array of schemas) for array types
//   - anyOf / oneOf (array of schemas) -> union of member types
//   - allOf (array of schemas) -> merged object/array types where possible; otherwise union approximation
//
// Notes:
//   - Unsupported or unrecognized keywords are ignored.
//   - enum/const and $ref are not resolved specially and are treated as unknown.
//
// Parameters:
//
//	schemaJSON []byte: The JSON bytes of a JSON Schema document to process.
//
// Returns:
//
//	error: An error if the schema cannot be parsed; otherwise nil.
func (s *InputJsonSchema) ProcessJSONSchema(schemaJSON []byte) error {
	// Parse with qri-io/jsonschema to respect JSON Schema structure & keywords
	rs := &qjsonschema.Schema{}
	if err := json.Unmarshal(schemaJSON, rs); err != nil {
		return err
	}
	// reset additionalProperties tracking
	s.additionalDefs = make(map[string]RegoTypeDef)
	s.additionalPaths = make(map[string]struct{})
	s.types = s.processQriSchemaAt(rs, nil)
	return nil
}

// ProcessInput implements InputSchemaAPI by delegating to ProcessJSONSchema.
// The input is expected to be a JSON Schema document (Draft-07-like subset).
//
// Parameters:
//
//	b []byte: The JSON bytes representing a JSON Schema document.
//
// Returns:
//
//	error: An error if parsing fails; otherwise nil.
func (s *InputJsonSchema) ProcessInput(b []byte) error { return s.ProcessJSONSchema(b) }

// GetType returns the RegoTypeDef for a given path in the input schema.
// Semantics match InputSchema.GetType.
//
// Parameters:
//
//	path []PathNode: The path to look up within the input schema.
//
// Returns:
//
//	*RegoTypeDef: The type definition found at the given path (if any).
//	bool: True if a type is found at the given path; otherwise false.
func (s *InputJsonSchema) GetType(path []PathNode) (*RegoTypeDef, bool) {
	// First try direct lookup.
	if t, ok := s.types.GetTypeFromPath(path); ok && t != nil {
		return t, true
	}
	// Fallback: consider JSON Schema additionalProperties along the path.
	// We'll traverse manually and delegate a single-step resolution to GetTypeFromPath
	// at each iteration. When a field is missing on an object that has additionalProperties,
	// we use the recorded additional type definition and retry the same path node.
	current := s.types
	segments := make([]string, 0, len(path))
	for i := 0; i < len(path); {
		pn := path[i]
		// Path key for additionalProperties lookup at this depth
		key := s.pathKeyFromSegments(segments)

		// If we're currently at a union, we cannot deterministically traverse further,
		// unless additionalProperties applies at this level.
		if current.IsUnion() {
			if _, hasAP := s.additionalPaths[key]; hasAP {
				ap := s.additionalDefs[key]
				segments = append(segments, "*")
				current = ap
				// consume this path node under additionalProperties and continue
				i++
				continue
			}
			return nil, false
		}

		// Try to resolve exactly one path node using the type's own logic.
		if stepType, ok := current.GetTypeFromPath(path[i : i+1]); ok && stepType != nil {
			// Update segments for additionalProperties path keying.
			if current.IsArray() {
				segments = append(segments, "[]")
			} else if current.IsObject() {
				if pn.IsGround {
					segments = append(segments, pn.Key)
				}
				// For non-ground object access we don't modify segments here;
				// if additionalProperties is needed, we will handle it when encountering a union/non-determinism.
			}
			current = *stepType
			// consumed this path node
			i++
			continue
		}

		// One-step resolution failed. If we're on an object and have additionalProperties,
		// switch to the additional type and retry the same path node.
		if current.IsObject() {
			if _, hasAP := s.additionalPaths[key]; hasAP {
				ap := s.additionalDefs[key]
				segments = append(segments, "*")
				current = ap
				// consume this path node and continue resolution under the additional schema
				i++
				continue
			}
			// No applicable additionalProperties. Deterministic traversal failed.
			return nil, false
		}

		// Array/atomic/unknown without a resolvable step cannot continue.
		return nil, false
	}
	// Consumed the entire path successfully.
	ret := current
	return &ret, true
}

// HasField checks if a field exists at the given path in the input schema.
// Semantics match InputSchema.HasField.
//
// Parameters:
//
//	path []string: The simple path segments to check.
//
// Returns:
//
//	bool: True if a field exists at the given path; otherwise false.
func (s *InputJsonSchema) HasField(path []string) bool {
	typ, ok := s.GetType(FromGroundPath(path))
	return ok && typ != nil
}

// GetTypes returns the complete type definition structure for the input schema.
// Semantics match InputSchema.GetTypes.
//
// Returns:
//
//	RegoTypeDef: The root type definition derived from the JSON Schema.
func (s *InputJsonSchema) GetTypes() RegoTypeDef {
	return s.types
}

// --------------------------
// JSON Schema processing (qri-io/jsonschema)
// --------------------------

// processQriSchema converts a qri-io/jsonschema Schema into a RegoTypeDef by
// interpreting core JSON Schema keywords (type, properties, items, anyOf, oneOf, allOf).
// Unknown or unsupported shapes are mapped to an unknown type.
//
// Parameters:
//
//	rs *qjsonschema.Schema: The parsed JSON Schema node to convert.
//
// Returns:
//
//	RegoTypeDef: The approximated Rego type for the given schema node.
func (s *InputJsonSchema) processQriSchema(rs *qjsonschema.Schema) RegoTypeDef {
	return s.processQriSchemaAt(rs, nil)
}

// processQriSchemaAt is the path-aware variant that records additionalProperties
// types along the given path.
func (s *InputJsonSchema) processQriSchemaAt(rs *qjsonschema.Schema, path []string) RegoTypeDef {
	if rs == nil {
		return NewUnknownType()
	}

	// First, handle combinators (anyOf/oneOf/allOf)
	if t, ok := s.tryCombinatorsAt(rs, path); ok {
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
		if t, ok := s.objectTypeFromPropertiesAt(rs, path); ok {
			return t
		}
		if t, ok := s.arrayTypeFromItemsAt(rs, path); ok {
			return t
		}
		// $ref or other unknowns
		return NewUnknownType()
	}

	if len(typeNames) > 1 {
		parts := make([]RegoTypeDef, 0, len(typeNames))
		for _, tn := range typeNames {
			parts = append(parts, s.processByTypeNameAt(rs, tn, path))
		}
		u := NewUnionType(parts)
		u.CanonizeUnion()
		return u
	}
	return s.processByTypeNameAt(rs, typeNames[0], path)
}

// extractTypeNames returns the list of JSON Schema type names (e.g., "object",
// "array", "string") from a qri Type, handling both single-string and array
// representations.
//
// Parameters:
//
//	t *qjsonschema.Type: The qri type wrapper to inspect.
//
// Returns:
//
//	[]string: The list of type names; empty if none could be determined.
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

// processByTypeNameAt builds a RegoTypeDef for a specific JSON Schema "type"
// value, delegating to object/array helpers when applicable.
//
// Parameters:
//
//	rs *qjsonschema.Schema: The schema node whose type is being interpreted.
//	typ string: The JSON Schema type name (e.g., "object", "array").
//
// Returns:
//
//	RegoTypeDef: The approximated type for the provided JSON Schema type name.
func (s *InputJsonSchema) processByTypeNameAt(rs *qjsonschema.Schema, typ string, path []string) RegoTypeDef {
	switch typ {
	case "object":
		if t, ok := s.objectTypeFromPropertiesAt(rs, path); ok {
			return t
		}
		return NewObjectType(map[string]RegoTypeDef{})
	case "array":
		if t, ok := s.arrayTypeFromItemsAt(rs, path); ok {
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

// tryCombinatorsAt handles anyOf/oneOf/allOf branches at the given path.
//
// Parameters:
//
//	rs *qjsonschema.Schema: The schema node to inspect for combinators.
//
// Returns:
//
//	RegoTypeDef: The computed type if a combinator was applied; zero value otherwise.
//	bool: True if a combinator was found and handled; otherwise false.
func (s *InputJsonSchema) tryCombinatorsAt(rs *qjsonschema.Schema, path []string) (RegoTypeDef, bool) {
	if v := rs.JSONProp("anyOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			u := s.unionFromSchemasAt(arr, path)
			return u, true
		}
	}
	if v := rs.JSONProp("oneOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			u := s.unionFromSchemasAt(arr, path)
			return u, true
		}
	}
	if v := rs.JSONProp("allOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			t := s.mergeAllOfAt(arr, path)
			return t, true
		}
	}
	return RegoTypeDef{}, false
}

// schemaSliceFromJSONProp converts anyOf/oneOf/allOf JSONProp values to a slice of schemas.
//
// Parameters:
//
//	v interface{}: The raw JSONProp value from qri's Schema.
//
// Returns:
//
//	[]*qjsonschema.Schema: The extracted list of subschemas (if any).
//	bool: True if the conversion succeeded; otherwise false.
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

// unionFromSchemasAt converts a slice of qri schemas to their RegoTypeDef union
// and canonizes it to remove duplicates.
//
// Parameters:
//
//	list []*qjsonschema.Schema: The list of subschemas to union.
//
// Returns:
//
//	RegoTypeDef: A union type representing the disjunction of the subschema types.
func (s *InputJsonSchema) unionFromSchemasAt(list []*qjsonschema.Schema, path []string) RegoTypeDef {
	parts := make([]RegoTypeDef, 0, len(list))
	for _, sub := range list {
		parts = append(parts, s.processQriSchemaAt(sub, path))
	}
	u := NewUnionType(parts)
	u.CanonizeUnion()
	return u
}

// mergeAllOfAt merges a list of schemas as in JSON Schema allOf by converting each
// to a RegoTypeDef and combining them with mergeTypes.
//
// Parameters:
//
//	list []*qjsonschema.Schema: The list of schemas to merge conjunctively.
//
// Returns:
//
//	RegoTypeDef: The merged type, approximating the conjunction of the input schemas.
func (s *InputJsonSchema) mergeAllOfAt(list []*qjsonschema.Schema, path []string) RegoTypeDef {
	if len(list) == 0 {
		return NewUnknownType()
	}
	acc := s.processQriSchemaAt(list[0], path)
	for i := 1; i < len(list); i++ {
		acc = mergeTypes(acc, s.processQriSchemaAt(list[i], path))
	}
	return acc
}

// objectTypeFromPropertiesAt builds an object RegoTypeDef from the "properties"
// keyword if present. If absent, returns an empty object type and records
// additionalProperties for this path when present.
//
// Parameters:
//
//	rs *qjsonschema.Schema: The schema node potentially containing properties.
//
// Returns:
//
//	RegoTypeDef: The object type with fields derived from properties (or empty if none).
//	bool: True if treated as an object (including when properties are absent);
//	      false only when the properties value cannot be interpreted.
func (s *InputJsonSchema) objectTypeFromPropertiesAt(rs *qjsonschema.Schema, path []string) (RegoTypeDef, bool) {
	// If the schema doesn't explicitly have a properties keyword, still capture additionalProperties
	if !rs.HasKeyword("properties") {
		s.maybeRecordAdditionalProperties(rs, path)
		return NewObjectType(map[string]RegoTypeDef{}), true
	}
	v := rs.JSONProp("properties")
	if v == nil {
		// Even without properties, additionalProperties may still apply to this object
		// Record it if present, and return an empty object.
		s.maybeRecordAdditionalProperties(rs, path)
		return NewObjectType(map[string]RegoTypeDef{}), true
	}
	fields := make(map[string]RegoTypeDef)
	switch props := v.(type) {
	case qjsonschema.Properties:
		for k, child := range props {
			fields[k] = s.processQriSchemaAt(child, append(path, k))
		}
	case *qjsonschema.Properties:
		if props != nil {
			for k, child := range *props {
				fields[k] = s.processQriSchemaAt(child, append(path, k))
			}
		}
	default:
		return RegoTypeDef{}, false
	}
	// Record additionalProperties type for this object if present
	s.maybeRecordAdditionalProperties(rs, path)
	return NewObjectType(fields), true
}

// arrayTypeFromItemsAt builds an array RegoTypeDef from the "items" keyword if present.
//
// Parameters:
//
//	rs *qjsonschema.Schema: The schema node potentially containing items.
//
// Returns:
//
//	RegoTypeDef: The array type with element type derived from items.
//	bool: True if items were found and processed; otherwise false.
func (s *InputJsonSchema) arrayTypeFromItemsAt(rs *qjsonschema.Schema, path []string) (RegoTypeDef, bool) {
	v := rs.JSONProp("items")
	if v == nil {
		return RegoTypeDef{}, false
	}
	switch items := v.(type) {
	case *qjsonschema.Items:
		if items == nil {
			return NewArrayType(NewUnknownType()), true
		}
		return arrayTypeFromItemSchemasAt(s, items.Schemas, path), true
	case qjsonschema.Items:
		return arrayTypeFromItemSchemasAt(s, items.Schemas, path), true
	default:
		return RegoTypeDef{}, false
	}
}

// arrayTypeFromItemSchemasAt returns an array type whose element type is derived
// from the provided item schemas (unknown for empty, direct type for one,
// union for multiple/tuple-style).
//
// Parameters:
//
//	conv *InputJsonSchema: Converter used to process subschemas.
//	schemas []*qjsonschema.Schema: The list of item schemas.
//
// Returns:
//
//	RegoTypeDef: The resulting array type with the computed element type.
func arrayTypeFromItemSchemasAt(conv *InputJsonSchema, schemas []*qjsonschema.Schema, basePath []string) RegoTypeDef {
	if len(schemas) == 0 {
		return NewArrayType(NewUnknownType())
	}
	if len(schemas) == 1 {
		et := conv.processQriSchemaAt(schemas[0], append(basePath, "[]"))
		return NewArrayType(et)
	}
	// tuple-style: union element type
	u := conv.unionFromSchemasAt(schemas, append(basePath, "[]"))
	return NewArrayType(u)
}

// maybeRecordAdditionalProperties inspects rs for additionalProperties and records
// the discovered type definition at the provided object path.
func (s *InputJsonSchema) maybeRecordAdditionalProperties(rs *qjsonschema.Schema, path []string) {
	v := rs.JSONProp("additionalProperties")
	if v == nil {
		return
	}
	key := s.pathKeyFromSegments(path)
	switch ap := v.(type) {
	case *qjsonschema.AdditionalProperties:
		if ap != nil {
			// Resolve to underlying *Schema
			sch := ap.Resolve(jptr.Pointer{}, "")
			if sch == nil {
				return
			}
			// Inspect marshaled form to detect boolean true/false vs object
			if b, err := sch.MarshalJSON(); err == nil {
				// Boolean true
				if string(b) == "true" {
					s.additionalPaths[key] = struct{}{}
					s.recordAdditionalType(key, NewUnknownType())
					return
				}
				// Boolean false -> do nothing
				if string(b) == "false" {
					return
				}
			}
			// Treat as schema
			s.additionalPaths[key] = struct{}{}
			t := s.processQriSchemaAt(sch, append(path, "*"))
			s.recordAdditionalType(key, t)
		}
	case qjsonschema.AdditionalProperties:
		// Take address to reuse pointer logic
		ap2 := ap
		sch := (&ap2).Resolve(jptr.Pointer{}, "")
		if sch == nil {
			return
		}
		if b, err := sch.MarshalJSON(); err == nil {
			if string(b) == "true" {
				s.additionalPaths[key] = struct{}{}
				s.recordAdditionalType(key, NewUnknownType())
				return
			}
			if string(b) == "false" {
				return
			}
		}
		s.additionalPaths[key] = struct{}{}
		t := s.processQriSchemaAt(sch, append(path, "*"))
		s.recordAdditionalType(key, t)
	case bool:
		if ap {
			s.additionalPaths[key] = struct{}{}
			// Unknown type if 'true'
			s.recordAdditionalType(key, NewUnknownType())
		}
	case *qjsonschema.Schema:
		if ap != nil {
			s.additionalPaths[key] = struct{}{}
			t := s.processQriSchemaAt(ap, append(path, "*"))
			s.recordAdditionalType(key, t)
		}
	case qjsonschema.Schema:
		t := s.processQriSchemaAt(&ap, append(path, "*"))
		s.additionalPaths[key] = struct{}{}
		s.recordAdditionalType(key, t)
	default:
		// Fallback: try to interpret unknown wrapper by JSON round-trip
		if b, err := json.Marshal(v); err == nil {
			var bval bool
			if err2 := json.Unmarshal(b, &bval); err2 == nil {
				if bval {
					s.additionalPaths[key] = struct{}{}
					s.recordAdditionalType(key, NewUnknownType())
				}
				return
			}
			tmp := &qjsonschema.Schema{}
			if err3 := json.Unmarshal(b, tmp); err3 == nil {
				s.additionalPaths[key] = struct{}{}
				t := s.processQriSchemaAt(tmp, append(path, "*"))
				s.recordAdditionalType(key, t)
				return
			}
		}
	}
}

// recordAdditionalType merges when a type is already recorded for a path (e.g., from anyOf/oneOf branches).
func (s *InputJsonSchema) recordAdditionalType(key string, t RegoTypeDef) {
	if existing, ok := s.additionalDefs[key]; ok {
		merged := mergeTypes(existing, t)
		s.additionalDefs[key] = merged
		return
	}
	s.additionalDefs[key] = t
}

// pathKeyFromSegments joins path segments using '/'. Arrays are represented by "[]".
func (s *InputJsonSchema) pathKeyFromSegments(segs []string) string {
	if len(segs) == 0 {
		return ""
	}
	return strings.Join(segs, "/")
}

// mergeTypes attempts to combine two RegoTypeDef values into a single, more precise type.
//
// Heuristics:
//   - If equal, return the type.
//   - If one is more precise than the other, return the more precise one.
//   - If both are objects, merge their fields (union of field sets, merging recursively).
//   - If both are arrays, merge element types recursively.
//   - Otherwise, return a union of both and canonize.
//
// Parameters:
//
//	a RegoTypeDef: The first type to merge.
//	b RegoTypeDef: The second type to merge.
//
// Returns:
//
//	RegoTypeDef: The merged, more precise type (or a union if no better merge exists).
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
