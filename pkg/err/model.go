package err

import (
	"errors"
	"fmt"
)

// Model decoding errors.
var (
	ErrUnsupportedSimpleValue = errors.New("model: unsupported simple z3 value")
	ErrUnsupportedOTypeValue  = errors.New("model: unsupported OType value")
	ErrNilZ3Context           = errors.New("model: nil Z3 context")
	ErrNilZ3Model             = errors.New("model: nil Z3 model")
)

// ErrMissingConstDecl reports that a named constant declaration was not
// recorded within the Z3 context, which prevents model evaluation.
func ErrMissingConstDecl(varName string) error {
	return fmt.Errorf("model: declaration for %s not recorded in context", varName)
}
