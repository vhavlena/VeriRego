// Package types provides type analysis for Rego AST.
package types

// InputSchemaAPI defines a common interface for input schema providers used by
// the type inference. Implementations can derive types from example instance
// documents (YAML/JSON) or from JSON Schemas while exposing a unified API.
//
// Semantics of GetType, HasField and GetTypes must be consistent across
// implementations to ensure stable type inference behavior.
type InputSchemaAPI interface {
	// ProcessInput ingests raw schema or example document bytes and prepares
	// the internal type representation used by GetType/HasField/GetTypes.
	// Implementations decide the exact format (e.g., YAML example or JSON Schema).
	ProcessInput(input []byte) error

	// GetType returns the RegoTypeDef for a given path in the input schema.
	GetType(path []PathNode) (*RegoTypeDef, bool)

	// HasField checks if a field exists at the given ground path in the input schema.
	HasField(path []string) bool

	// GetTypes returns the complete type definition structure for the input schema.
	GetTypes() RegoTypeDef
}
