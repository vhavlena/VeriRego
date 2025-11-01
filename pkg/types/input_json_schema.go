// Package types provides type analysis for Rego AST.
package types

import (
	"encoding/json"

	jptr "github.com/qri-io/jsonpointer"
	qjsonschema "github.com/qri-io/jsonschema"
)

const (
	// AdditionalPropertiesKey is the special key used in ObjectFields to store
	// the type for additionalProperties from JSON Schema.
	AdditionalPropertiesKey = "*"
	DisabledAdditional      = "-*"
)

// InputJsonSchema stores type information derived from a JSON Schema document.
// It mirrors the semantics of InputSchema but derives the RegoTypeDef from a JSON Schema
// instead of an example YAML/JSON instance document.
// AdditionalProperties are stored directly in the types structure: when an object has
// additionalProperties, we add a special AdditionalPropertiesKey to ObjectFields with the type for additional properties.
type InputJsonSchema struct {
	types RegoTypeDef
}

// NewInputJsonSchema creates and returns a new InputJsonSchema instance with an empty object type definition.
//
// Returns:
//
//	*InputJsonSchema: A new instance with an empty object type definition.
func NewInputJsonSchema() *InputJsonSchema {
	return &InputJsonSchema{
		types: NewObjectType(make(map[string]RegoTypeDef)),
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
	s.types = s.processQriSchema(rs)
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
	// Try direct lookup first
	if t, ok := s.types.GetTypeFromPath(path); ok && t != nil {
		return t, true
	}

	// If direct lookup fails, traverse manually to check for additionalProperties ("*" key)
	current := s.types
	for i := 0; i < len(path); i++ {
		pn := path[i]
		remainingPath := path[i+1:]

		if current.IsUnion() {
			// For unions, try to resolve through each member and collect results
			var results []RegoTypeDef
			for _, member := range current.Union {
				// Create a temporary schema with this member as root
				tempSchema := &InputJsonSchema{types: member}
				if result, ok := tempSchema.GetType(path[i:]); ok && result != nil {
					results = append(results, *result)
				}
			}
			if len(results) == 0 {
				return nil, false
			}
			if len(results) == 1 {
				return &results[0], true
			}
			// Return union of results
			unionResult := NewUnionType(results)
			unionResult.CanonizeUnion()
			return &unionResult, true
		} else if current.IsObject() {
			// Try exact field match first
			if stepType, ok := current.GetTypeFromPath(path[i : i+1]); ok && stepType != nil {
				current = *stepType
				continue
			}

			// Field not found - check for additionalProperties
			if pn.IsGround {
				if apType, ok := current.ObjectFields[AdditionalPropertiesKey]; ok {
					// Use additionalProperties type for this field
					if len(remainingPath) == 0 {
						return &apType, true
					}
					// Continue traversal with the additionalProperties type
					current = apType
					continue
				}
			}
			// No match and no additionalProperties
			return nil, false
		} else if current.IsArray() {
			// Delegate to GetTypeFromPath for arrays
			if stepType, ok := current.GetTypeFromPath(path[i : i+1]); ok && stepType != nil {
				current = *stepType
				continue
			}
			return nil, false
		} else {
			// Cannot continue traversal
			return nil, false
		}
	}

	return &current, true
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
	if rs == nil {
		return NewUnknownType()
	}

	// First, handle combinators (anyOf/oneOf/allOf)
	if t, ok := s.tryCombinatorsAt(rs); ok {
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
		if t, ok := s.objectTypeFromPropertiesAt(rs); ok {
			return t
		}
		if t, ok := s.arrayTypeFromItemsAt(rs); ok {
			return t
		}
		// $ref or other unknowns
		return NewUnknownType()
	}

	if len(typeNames) > 1 {
		parts := make([]RegoTypeDef, 0, len(typeNames))
		for _, tn := range typeNames {
			parts = append(parts, s.processByTypeNameAt(rs, tn))
		}
		u := NewUnionType(parts)
		u.CanonizeUnion()
		return u
	}
	return s.processByTypeNameAt(rs, typeNames[0])
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

// processByTypeName builds a RegoTypeDef for a specific JSON Schema "type"
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
func (s *InputJsonSchema) processByTypeNameAt(rs *qjsonschema.Schema, typ string) RegoTypeDef {
	switch typ {
	case "object":
		if t, ok := s.objectTypeFromPropertiesAt(rs); ok {
			return t
		}
		return NewObjectType(map[string]RegoTypeDef{})
	case "array":
		if t, ok := s.arrayTypeFromItemsAt(rs); ok {
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

// tryCombinatorsAt handles anyOf/oneOf/allOf branches.
//
// Parameters:
//
//	rs *qjsonschema.Schema: The schema node to inspect for combinators.
//
// Returns:
//
//	RegoTypeDef: The computed type if a combinator was applied; zero value otherwise.
//	bool: True if a combinator was found and handled; otherwise false.
func (s *InputJsonSchema) tryCombinatorsAt(rs *qjsonschema.Schema) (RegoTypeDef, bool) {
	if v := rs.JSONProp("anyOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			u := s.unionFromSchemasAt(arr)
			return u, true
		}
	}
	if v := rs.JSONProp("oneOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			u := s.unionFromSchemasAt(arr)
			return u, true
		}
	}
	if v := rs.JSONProp("allOf"); v != nil {
		if arr, ok := schemaSliceFromJSONProp(v); ok && len(arr) > 0 {
			t := s.mergeAllOfAt(arr)
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
	case *qjsonschema.AnyOf:
		if s == nil {
			return nil, false
		}
		return []*qjsonschema.Schema(*s), true
	case *qjsonschema.OneOf:
		if s == nil {
			return nil, false
		}
		return []*qjsonschema.Schema(*s), true
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
func (s *InputJsonSchema) unionFromSchemasAt(list []*qjsonschema.Schema) RegoTypeDef {
	parts := make([]RegoTypeDef, 0, len(list))
	for _, sub := range list {
		parts = append(parts, s.processQriSchema(sub))
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
func (s *InputJsonSchema) mergeAllOfAt(list []*qjsonschema.Schema) RegoTypeDef {
	if len(list) == 0 {
		return NewUnknownType()
	}
	acc := s.processQriSchema(list[0])
	for i := 1; i < len(list); i++ {
		acc = mergeTypes(acc, s.processQriSchema(list[i]))
	}
	return acc
}

// objectTypeFromPropertiesAt builds an object RegoTypeDef from the "properties"
// keyword if present. If absent, returns an empty object type and records
// additionalProperties when present.
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
func (s *InputJsonSchema) objectTypeFromPropertiesAt(rs *qjsonschema.Schema) (RegoTypeDef, bool) {
	fields := make(map[string]RegoTypeDef)

	// Process properties if present
	if rs.HasKeyword("properties") {
		v := rs.JSONProp("properties")
		if v != nil {
			switch props := v.(type) {
			case *qjsonschema.Properties:
				if props != nil {
					for k, child := range *props {
						fields[k] = s.processQriSchema(child)
					}
				}
			default:
				return RegoTypeDef{}, false
			}
		}
	}

	// Create object type and set additionalProperties if present
	objType := NewObjectType(fields)
	if apType, isFalse := s.extractAdditionalProperties(rs); isFalse {
		// additionalProperties is explicitly false
		objType.ObjectFields[DisabledAdditional] = NewAtomicType(AtomicBoolean)
	} else if apType != nil {
		// additionalProperties is a schema or true
		objType.ObjectFields[AdditionalPropertiesKey] = *apType
	}
	return objType, true
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
func (s *InputJsonSchema) arrayTypeFromItemsAt(rs *qjsonschema.Schema) (RegoTypeDef, bool) {
	v := rs.JSONProp("items")
	if v == nil {
		return RegoTypeDef{}, false
	}
	switch items := v.(type) {
	case *qjsonschema.Items:
		if items == nil {
			return NewArrayType(NewUnknownType()), true
		}
		return arrayTypeFromItemSchemasAt(s, items.Schemas), true
	// case qjsonschema.Items:
	// 	return arrayTypeFromItemSchemasAt(s, items.Schemas), true
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
func arrayTypeFromItemSchemasAt(conv *InputJsonSchema, schemas []*qjsonschema.Schema) RegoTypeDef {
	if len(schemas) == 0 {
		return NewArrayType(NewUnknownType())
	}
	if len(schemas) == 1 {
		et := conv.processQriSchema(schemas[0])
		return NewArrayType(et)
	}
	// tuple-style: union element type
	u := conv.unionFromSchemasAt(schemas)
	return NewArrayType(u)
}

// extractAdditionalProperties inspects rs for additionalProperties and returns
// the type definition if present, along with a flag indicating if it's explicitly false.
// Returns (type, isFalse) where:
//   - type is nil if additionalProperties is not present or is false
//   - type is the schema type if additionalProperties is a schema or true
//   - isFalse is true only when additionalProperties is explicitly set to false
func (s *InputJsonSchema) extractAdditionalProperties(rs *qjsonschema.Schema) (*RegoTypeDef, bool) {
	v := rs.JSONProp("additionalProperties")
	if v == nil {
		return nil, false
	}

	switch ap := v.(type) {
	case *qjsonschema.AdditionalProperties:
		if ap != nil {
			// Resolve to underlying *Schema
			sch := ap.Resolve(jptr.Pointer{}, "")
			if sch == nil {
				return nil, false
			}
			// Inspect marshaled form to detect boolean true/false vs object
			if b, err := sch.MarshalJSON(); err == nil {
				// Boolean true
				if string(b) == "true" {
					t := NewUnknownType()
					return &t, false
				}
				// Boolean false -> return flag
				if string(b) == "false" {
					return nil, true
				}
			}
			// Treat as schema
			t := s.processQriSchema(sch)
			return &t, false
		}
	case bool:
		if ap {
			// Unknown type if 'true'
			t := NewUnknownType()
			return &t, false
		}
		// Return flag for false
		return nil, true
	case *qjsonschema.Schema:
		if ap != nil {
			t := s.processQriSchema(ap)
			return &t, false
		}
	default:
		// Fallback: try to interpret unknown wrapper by JSON round-trip
		if b, err := json.Marshal(v); err == nil {
			var bval bool
			if err2 := json.Unmarshal(b, &bval); err2 == nil {
				if bval {
					t := NewUnknownType()
					return &t, false
				}
				// Return flag for false
				return nil, true
			}
			tmp := &qjsonschema.Schema{}
			if err3 := json.Unmarshal(b, tmp); err3 == nil {
				t := s.processQriSchema(tmp)
				return &t, false
			}
		}
	}
	return nil, false
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
