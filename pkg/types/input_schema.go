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

// NewInputSchema creates and returns a new InputSchema instance with an empty object type definition.
//
// Returns:
//
//	*InputSchema: A new InputSchema instance.
func NewInputSchema() *InputSchema {
	return &InputSchema{
		types: NewObjectType(make(map[string]RegoTypeDef)),
	}
}

// ProcessYAMLInput processes a YAML input file, extracts type information from the 'input' field, and updates the InputSchema.
//
// Parameters:
//
//	yamlData ([]byte): The YAML data to process.
//
// Returns:
//
//	error: An error if the YAML cannot be unmarshaled, otherwise nil.
func (s *InputSchema) ProcessYAMLInput(yamlData []byte) error {
	var data map[string]interface{}
	if err := yaml.Unmarshal(yamlData, &data); err != nil {
		return fmt.Errorf("failed to unmarshal input: %w", err)
	}

	s.types = s.processNode(data)

	return nil
}

// processNode recursively processes a node in the YAML structure and returns the corresponding RegoTypeDef.
// Handles objects, arrays, strings, numbers, booleans, and unknown types.
//
// Parameters:
//
//	node (interface{}): The YAML node to process.
//
// Returns:
//
//	RegoTypeDef: The type definition for the node.
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
	case nil:
		return NewAtomicType(AtomicNull)
	default:
		return NewUnknownType()
	}
}

// GetType returns the RegoTypeDef for a given path in the input schema.
//
// Parameters:
//
//	path ([]PathNode): A slice of PathNode representing nested field names.
//
// Returns:
//
//	*RegoTypeDef: The type definition for the path, if found.
//	bool: True if the path exists, false otherwise.
func (s *InputSchema) GetType(path []PathNode) (*RegoTypeDef, bool) {
	return s.types.GetTypeFromPath(path)
}

// HasField checks if a field exists at the given path in the input schema.
//
// Parameters:
//
//	path ([]string): A slice of strings representing nested field names.
//
// Returns:
//
//	bool: True if the field exists, false otherwise.
func (s *InputSchema) HasField(path []string) bool {
	typ, exists := s.GetType(FromGroundPath(path))
	return exists && typ != nil
}

// GetTypes returns the complete type definition structure for the input schema.
//
// Returns:
//
//	RegoTypeDef: The complete type definition structure.
func (s *InputSchema) GetTypes() RegoTypeDef {
	return s.types
}
