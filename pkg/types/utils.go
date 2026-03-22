package types

import (
	"github.com/open-policy-agent/opa/v1/ast"
)

// isVar reports whether the provided AST term's value is a variable
// (i.e. an `ast.Var`).
func isVar(term *ast.Term) bool {
	_, c := term.Value.(ast.Var)
	return c
}

// LiteralTermType returns the RegoTypeDef for a literal AST term.
// For non-literal terms (variables, refs, …) it returns NewUnknownType().
func LiteralTermType(term *ast.Term) RegoTypeDef {
	if term == nil {
		return NewUnknownType()
	}
	switch term.Value.(type) {
	case ast.String:
		return NewAtomicType(AtomicString)
	case ast.Number:
		return NewAtomicType(AtomicInt)
	case ast.Boolean:
		return NewAtomicType(AtomicBoolean)
	case ast.Null:
		return NewAtomicType(AtomicNull)
	case *ast.Array:
		return NewArrayType(NewUnknownType())
	case ast.Object:
		return NewObjectType(make(map[string]RegoTypeDef))
	default:
		return NewUnknownType()
	}
}

// IsEqualityOp reports whether op is an OPA equality/assignment operator.
func IsEqualityOp(op string) bool {
	switch op {
	case "eq", "assign", "unify":
		return true
	}
	return false
}

// IsNumericCompOp reports whether op is an OPA numeric comparison operator.
func IsNumericCompOp(op string) bool {
	switch op {
	case "gt", "lt", "gte", "lte":
		return true
	}
	return false
}
