// Package err defines common errors for the VeriRego project.
package err

import (
	"errors"
	"fmt"
)

var (
	ErrNotObjectType     = errors.New("expected object type")
	ErrUnsupportedType   = errors.New("unsupported type")
	ErrUnsupportedAtomic = errors.New("unsupported atomic type")
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
