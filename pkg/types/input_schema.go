// Package types provides type analysis for Rego AST.
package types

import (
	"fmt"

	"sigs.k8s.io/yaml"
)

// InputSchema stores type information for input fields
type InputSchema struct {
	types map[string]RegoType
}

// NewInputSchema creates a new InputSchema instance
func NewInputSchema() *InputSchema {
	return &InputSchema{
		types: make(map[string]RegoType),
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
		s.processNode("input", inputData)
	}
	return nil
}

// processNode processes a node in the YAML structure and assigns types
func (s *InputSchema) processNode(path string, node interface{}) {
	switch nodeValue := node.(type) {
	case map[string]interface{}:
		s.types[path] = TypeObject
		for key, value := range nodeValue {
			newPath := path + "." + key
			s.processNode(newPath, value)
		}
	case []interface{}:
		s.types[path] = TypeArray
		if len(nodeValue) > 0 {
			// Process the first element to get the type of array elements
			s.processNode(path+"[0]", nodeValue[0])
		}
	case string:
		s.types[path] = TypeString
	case float64, int:
		s.types[path] = TypeInt
	case bool:
		s.types[path] = TypeBoolean
	}
}
