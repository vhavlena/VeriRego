package schemainfer

import (
	"encoding/json"
	"sort"

	"github.com/vhavlena/verirego/pkg/types"
)

// JSONSchema is a minimal JSON Schema (Draft-07) representation.
// Only the fields needed to express types inferred by SchemaInferrer are included.
type JSONSchema struct {
	Schema               string                 `json:"$schema,omitempty"`
	Type                 interface{}            `json:"type,omitempty"` // string or []string
	Properties           map[string]*JSONSchema `json:"properties,omitempty"`
	Items                *JSONSchema            `json:"items,omitempty"`
	AdditionalProperties interface{}            `json:"additionalProperties,omitempty"` // bool or *JSONSchema
}

// MarshalIndent serializes the schema to indented JSON.
func (s *JSONSchema) MarshalIndent() ([]byte, error) {
	return json.MarshalIndent(s, "", "  ")
}

// ToJSONSchema converts a SchemaNode tree produced by SchemaInferrer into a JSONSchema.
// topLevel should be true for the root call; it adds the $schema field.
func ToJSONSchema(node *SchemaNode, topLevel bool) *JSONSchema {
	if node == nil {
		return &JSONSchema{Type: "unknown"}
	}

	schema := &JSONSchema{}
	if topLevel {
		schema.Schema = "http://json-schema.org/draft-07/schema#"
	}

	et := effectiveType(node)
	switch et.Kind {
	case types.KindAtomic:
		switch et.AtomicType {
		case types.AtomicString:
			schema.Type = "string"
		case types.AtomicInt:
			schema.Type = "integer"
		case types.AtomicBoolean:
			schema.Type = "boolean"
		case types.AtomicNull:
			schema.Type = "null"
		}

	case types.KindArray:
		schema.Type = "array"
		if node.Items != nil {
			schema.Items = ToJSONSchema(node.Items, false)
		} else {
			schema.Items = &JSONSchema{Type: "unknown"}
		}

	case types.KindObject:
		schema.Type = "object"
		if node.AdditionalProperties != nil && len(node.Properties) == 0 {
			// Dynamic-key object: emit additionalProperties as a schema.
			schema.AdditionalProperties = ToJSONSchema(node.AdditionalProperties, false)
		} else if len(node.Properties) > 0 {
			// Known-field object: enumerate properties and disallow extras.
			schema.Properties = make(map[string]*JSONSchema, len(node.Properties))
			keys := make([]string, 0, len(node.Properties))
			for k := range node.Properties {
				keys = append(keys, k)
			}
			sort.Strings(keys)
			for _, k := range keys {
				schema.Properties[k] = ToJSONSchema(node.Properties[k], false)
			}
			schema.AdditionalProperties = false
		}

	default:
		// KindUnknown: emit "unknown" so users know they must concretize this type.
		schema.Type = "unknown"
	}

	return schema
}
