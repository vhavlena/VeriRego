package main

import (
	"strings"
	"github.com/open-policy-agent/opa/ast"
	// "fmt"
	// "reflect"
)

// StringOperations represents a collection of string operations found during AST traversal.
// It implements the PropagatedValue interface and keeps track of all string manipulation
// operations encountered in the Rego policy.
type StringOperations struct {
	operations []string
}

// NewStringOperations creates a new StringOperations instance with an empty
// operations slice. It initializes the internal slice that will be used to
// track string operations.
func NewStringOperations() *StringOperations {
	return &StringOperations{
		operations: make([]string, 0),
	}
}

// Join combines this StringOperations with another PropagatedValue by merging their operations.
// If the other value is nil, it returns the current instance unchanged. The method expects
// the other value to be of type *StringOperations.
func (s *StringOperations) Join(other PropagatedValue) PropagatedValue {
	if other == nil {
		return s
	}
	otherOps := other.(*StringOperations)
	joined := &StringOperations{
		operations: make([]string, len(s.operations)+len(otherOps.operations)),
	}
	copy(joined.operations, s.operations)
	copy(joined.operations[len(s.operations):], otherOps.operations)
	return joined
}

// FromBasicTerm creates a new PropagatedValue from a basic term (leaf term or function call).
// It examines the term to determine if it represents a string operation and returns a new
// StringOperations instance containing the operation if found, or an empty instance if not.
func (s *StringOperations) FromBasicTerm(term *ast.Term) PropagatedValue {
	if term == nil {
		return NewStringOperations()
	}

	//fmt.Printf(":: %v %v\n", reflect.TypeOf(term.Value).String(), term)

	switch val := term.Value.(type) {
	case ast.Ref:
		if isStringOperation(val.String()) {
			return &StringOperations{
				operations: []string{val[0].String()},
			}
		}
	case ast.Call:
		// Check if the reference is to a string operation
		if len(val) > 0 {
			firstTerm := val[0].String()
			if isStringOperation(firstTerm) {
				return &StringOperations{
					operations: []string{firstTerm},
				}
			}
		}
	}
	
	return NewStringOperations()
}

// IsEmpty returns true if there are no string operations recorded in this instance.
// It checks if the internal operations slice is empty.
func (s *StringOperations) IsEmpty() bool {
	return len(s.operations) == 0
}

// stringOperationsList contains all recognized Rego string operations that the analyzer
// will detect and track during policy analysis.
var stringOperationsList = []string{
	"concat",
	"contains",
	"endswith",
	"format_int",
	"indexof",
	"lower",
	"replace",
	"split",
	"startswith",
	"substring",
	"trim",
	"upper",
	"regex.split",
	"regex.match",
	"regex.replace",
	"semver.compare",
}

// isStringOperation checks if an operation name matches any known string operation
// by comparing it against the stringOperationsList. For operations with dot notation,
// only the part after the last dot is compared.
func isStringOperation(name string) bool {
	cleanName := name
	if idx := strings.LastIndex(name, "."); idx != -1 {
		cleanName = name[idx+1:]
	}
	
	for _, op := range stringOperationsList {
		if idx := strings.LastIndex(op, "."); idx != -1 {
			op = op[idx+1:]
		}
		if cleanName == op {
			return true
		}
	}
	return false
}