package schemainfer

import (
	"encoding/json"
	"sort"
)

// JSONSchema is a minimal JSON Schema (Draft-07) representation.
// Only the fields needed to express types inferred by SchemaInferrer are included.
type JSONSchema struct {
	Schema               string                 `json:"$schema,omitempty"`
	Type                 interface{}            `json:"type,omitempty"` // string or []string
	Properties           map[string]*JSONSchema `json:"properties,omitempty"`
	Items                *JSONSchema            `json:"items,omitempty"`
	AdditionalProperties *bool                  `json:"additionalProperties,omitempty"`
}

// MarshalIndent serializes the schema to indented JSON.
func (s *JSONSchema) MarshalIndent() ([]byte, error) {
	return json.MarshalIndent(s, "", "  ")
}

// ToJSONSchema converts a SchemaNode tree produced by SchemaInferrer into a JSONSchema.
// topLevel should be true for the root call; it adds the $schema field.
func ToJSONSchema(node *SchemaNode, topLevel bool) *JSONSchema {
	if node == nil {
		return &JSONSchema{}
	}

	schema := &JSONSchema{}
	if topLevel {
		schema.Schema = "http://json-schema.org/draft-07/schema#"
	}

	switch effectiveHint(node) {
	case HintString:
		schema.Type = "string"

	case HintInteger:
		schema.Type = "integer"

	case HintBoolean:
		schema.Type = "boolean"

	case HintNull:
		schema.Type = "null"

	case HintArray:
		schema.Type = "array"
		if node.Items != nil {
			schema.Items = ToJSONSchema(node.Items, false)
		} else {
			schema.Items = &JSONSchema{}
		}

	case HintObject:
		schema.Type = "object"
		if len(node.Properties) > 0 {
			schema.Properties = make(map[string]*JSONSchema, len(node.Properties))
			// Sort keys for deterministic output.
			keys := make([]string, 0, len(node.Properties))
			for k := range node.Properties {
				keys = append(keys, k)
			}
			sort.Strings(keys)
			for _, k := range keys {
				schema.Properties[k] = ToJSONSchema(node.Properties[k], false)
			}
			f := false
			schema.AdditionalProperties = &f
		}

	default:
		// HintUnknown: emit an empty schema (matches anything)
	}

	return schema
}

// effectiveHint resolves the best hint for a node, taking structural evidence
// (presence of Properties or Items) into account when the explicit Hint is unknown.
func effectiveHint(node *SchemaNode) TypeHint {
	if node.Hint != HintUnknown {
		return node.Hint
	}
	if len(node.Properties) > 0 {
		return HintObject
	}
	if node.Items != nil {
		return HintArray
	}
	return HintUnknown
}
