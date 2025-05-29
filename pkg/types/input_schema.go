// Package types provides type analysis for Rego AST.
package types

import (
	"fmt"

	"sigs.k8s.io/yaml"
)

// InputSchema stores type information for input fields using RegoTypeDef
type InputSchema struct {
	types RegoTypeDef
}

// NewInputSchema creates a new InputSchema instance
func NewInputSchema() *InputSchema {
	return &InputSchema{
		types: NewObjectType(make(map[string]RegoTypeDef)),
	}
}

// ProcessYAMLInput processes a YAML input file to extract type information
func (s *InputSchema) ProcessYAMLInput(yamlData []byte) error {
	var data map[string]interface{}
	if err := yaml.Unmarshal(yamlData, &data); err != nil {
		return fmt.Errorf("failed to unmarshal input: %w", err)
	}

	// Start from the input object
	if inputData, ok := data["input"].(map[string]interface{}); ok {
		s.types = s.processNode(inputData)
	}
	return nil
}

// processNode processes a node in the YAML structure and returns RegoTypeDef
func (s *InputSchema) processNode(node interface{}) RegoTypeDef {
	switch nodeValue := node.(type) {
	case map[string]interface{}:
		fields := make(map[string]RegoTypeDef)
		for key, value := range nodeValue {
			fields[key] = s.processNode(value)
		}
		return NewObjectType(fields)
	case []interface{}:
		if len(nodeValue) > 0 {
			// Process the first element to get the type of array elements
			elementType := s.processNode(nodeValue[0])
			return NewArrayType(elementType)
		}
		// Empty array defaults to unknown element type
		return NewArrayType(NewUnknownType())
	case string:
		return NewAtomicType(AtomicString)
	case float64, int:
		return NewAtomicType(AtomicInt)
	case bool:
		return NewAtomicType(AtomicBoolean)
	default:
		return NewUnknownType()
	}
}

// GetType returns the RegoTypeDef for a given path
func (s *InputSchema) GetType(path []string) (*RegoTypeDef, bool) {
	return s.types.GetTypeFromPath(path)
}

// HasField checks if a field exists at the given path
func (s *InputSchema) HasField(path []string) bool {
	typ, exists := s.GetType(path)
	return exists && typ != nil
}

// GetTypes returns the complete type definition structure
func (s *InputSchema) GetTypes() RegoTypeDef {
	return s.types
}
