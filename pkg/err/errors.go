package err

import (
	"errors"
	"fmt"
)

func ErrNotObjectType(term string) error {
	return fmt.Errorf("expected object type for term %s", term)
}

func ErrInvalidInt(orig string) error {
	return fmt.Errorf(`failed to get number from "%s"`, orig)
}

func ErrUnsupportedType(term, tp string) error {
	return fmt.Errorf("unsupported type (%s) for term %s", tp, term)
}

func ErrUnsupportedAtomic(tp string) error {
	return fmt.Errorf(`unsupported atomic type "%s"`, tp)
}

func ErrUnexpectedValueType(val, expected string) error {
	return fmt.Errorf(`value "%s" does not have expected type "%s"`, val, expected)
}

var (
	ErrMissingSpecField  = errors.New("missing 'spec' field in YAML")
	ErrInvalidParameters = errors.New("missing or invalid 'spec.parameters' field in YAML")
)

// error signs
var (
	ErrUnsupportedTypeSign = errors.New("ErrUnsupportedTypeSign")
	ErrNotObjectTypeSign = errors.New("ErrNotObjectTypeSign")
)

func ErrNotImplemented(msg string) error {
	return fmt.Errorf("not implemented: %s", msg)
}

func ErrUnsupportedFunction(name string) error {
	return fmt.Errorf(`unsupported function: "%s"`, name)
}

func ErrTypeNotFound(term string) error {
	return fmt.Errorf(`type not found for term "%s"`, term)
}

func ErrFunctionNotFound(name string) error {
	return fmt.Errorf(`function "%s" not found`, name)
}

func ErrMissingObjectKey(obj, key string) error {
	return fmt.Errorf(`object "%s" is missing key "%s"`, obj, key)
}

// SMT-LIB/term conversion errors
var (
	ErrUnsupportedTermType          = errors.New("unsupported term type")
	ErrUnexpected                   = errors.New("unexpected error") // for states which should be unreachable
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
