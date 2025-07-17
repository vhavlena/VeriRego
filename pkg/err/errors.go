package err

import (
	"errors"
	"fmt"
)

var (
	ErrNotObjectType     = errors.New("expected object type")
	ErrUnsupportedType   = errors.New("unsupported type")
	ErrUnsupportedAtomic = errors.New("unsupported atomic type")
	ErrMissingSpecField  = errors.New("missing 'spec' field in YAML")
	ErrInvalidParameters = errors.New("missing or invalid 'spec.parameters' field in YAML")
)

// SMT-LIB/term conversion errors
var (
	ErrExplicitArraysNotSupported   = errors.New("explicit arrays are not supported")
	ErrObjectConversionNotSupported = errors.New("object conversion not supported")
	ErrSetConversionNotSupported    = errors.New("set conversion not supported")
	ErrUnsupportedTermType          = errors.New("unsupported term type")
	ErrUnsupportedFunction          = errors.New("unsupported function")
	ErrSchemaVarTypeNotFound        = errors.New("type for schema variable not found")
	ErrEmptyReferenceConv           = errors.New("Cannot convert empty reference")
	ErrInvalidEmptyTerm             = errors.New("invalid or empty expression terms")
)

// ErrSmtConstraints returns an error for SMT constraint generation failure.
//
// Parameters:
//
//	cause error: The underlying error.
//
// Returns:
//
//	error: The formatted error.
func ErrSmtConstraints(cause error) error {
	return fmt.Errorf("failed to get SMT constraints: %w", cause)
}

// ErrSmtFieldConstraints returns an error for SMT constraint generation failure for a specific field.
//
// Parameters:
//
//	field string: The field name.
//	cause error: The underlying error.
//
// Returns:
//
//	error: The formatted error.
func ErrSmtFieldConstraints(field string, cause error) error {
	return fmt.Errorf("failed to get SMT constraints for field %s: %w", field, cause)
}

// ErrYamlUnmarshal returns an error for YAML unmarshaling failure.
//
// Parameters:
//
//	cause error: The underlying error.
//
// Returns:
//
//	error: The formatted error.
func ErrYamlUnmarshal(cause error) error {
	return fmt.Errorf("failed to unmarshal YAML: %w", cause)
}
