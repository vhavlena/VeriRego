// Code related to predefined/builtin function typing rules.
package types

// PredefFunction captures typing rules for predefined/builtin functions.
//
// Fields:
//   - ReturnType: the function's return type
//   - CheckArity: validator for number of parameters (arity); should return true if ok
//   - UpdateParams: mutates provided parameter type expectations in-place to refine types
//     (commonly used to set all parameters to the same atomic type)
type PredefFunction struct {
	ReturnType   RegoTypeDef
	CheckArity   func(n int) bool
	UpdateParams func(pars []RegoTypeDef)
}

const (
	arityUnary   = 1
	arityBinary  = 2
	arityTernary = 3
)

// makeUpdateParamsAtomic creates an UpdateParams function that assigns the same
// atomic type to all parameters.
//
// Parameters:
//
//	a AtomicType: The atomic type to apply to each parameter.
//
// Returns:
//
//	func([]RegoTypeDef): A function that updates the provided parameter slice in place.
func makeUpdateParamsAtomic(a AtomicType) func([]RegoTypeDef) {
	return func(pars []RegoTypeDef) {
		for i := range pars {
			pars[i] = NewAtomicType(a)
		}
	}
}

// getPredefFunctions returns the registry of predefined/builtin functions and
// their typing behavior.
//
// Returns:
//
//	map[string]PredefFunction: A mapping from function name to its typing rules.
func getPredefFunctions() map[string]PredefFunction {
	return map[string]PredefFunction{
		// String operations: all params are strings, return string
		"trim": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"trim_left": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"replace": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"concat": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"format": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"lower": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n == arityBinary }, // lower(string, ret)
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"upper": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n == arityBinary }, // upper(string, ret)
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"split": {
			ReturnType:   NewAtomicType(AtomicString),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicString),
		},
		"semver.compare": {
			ReturnType: NewAtomicType(AtomicBoolean),
			CheckArity: func(n int) bool { return n == arityTernary },
			UpdateParams: func(pars []RegoTypeDef) {
				pars[0] = NewAtomicType(AtomicString)
				pars[1] = NewAtomicType(AtomicString)
				pars[2] = NewAtomicType(AtomicInt)
			},
		},

		// Numeric operations: all params are ints, return int
		"plus": {
			ReturnType:   NewAtomicType(AtomicInt),
			CheckArity:   func(n int) bool { return n >= arityBinary },
			UpdateParams: makeUpdateParamsAtomic(AtomicInt),
		},
		"minus": {
			ReturnType:   NewAtomicType(AtomicInt),
			CheckArity:   func(n int) bool { return n >= arityUnary },
			UpdateParams: makeUpdateParamsAtomic(AtomicInt),
		},
		"mul": {
			ReturnType:   NewAtomicType(AtomicInt),
			CheckArity:   func(n int) bool { return n >= arityBinary },
			UpdateParams: makeUpdateParamsAtomic(AtomicInt),
		},
		"div": {
			ReturnType:   NewAtomicType(AtomicInt),
			CheckArity:   func(n int) bool { return n >= arityBinary },
			UpdateParams: makeUpdateParamsAtomic(AtomicInt),
		},

		// Boolean operations: return boolean; keep parameter expectations unchanged (generic)
		"neq": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"and": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"or": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"not": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityUnary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"lt": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"contains": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"startswith": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},
		"endswith": {
			ReturnType:   NewAtomicType(AtomicBoolean),
			CheckArity:   func(n int) bool { return n == arityBinary },
			UpdateParams: func(_ []RegoTypeDef) {},
		},

		// Special-case: sprintf modeled as predicate returning boolean; first and last params must be strings
		"sprintf": {
			ReturnType: NewAtomicType(AtomicBoolean),
			CheckArity: func(n int) bool { return n >= arityBinary },
			UpdateParams: func(pars []RegoTypeDef) {
				if len(pars) >= arityUnary {
					pars[0] = NewAtomicType(AtomicString)
				}
				if len(pars) >= arityBinary {
					pars[len(pars)-1] = NewAtomicType(AtomicString)
				}
			},
		},
	}
}
