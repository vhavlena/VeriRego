package types

import (
	"fmt"

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

// exprLocKey returns a unique string key for an expression's source location.
func exprLocKey(expr *ast.Expr) string {
	if expr.Location == nil {
		return ""
	}
	return fmt.Sprintf("%s:%d:%d", expr.Location.File, expr.Location.Row, expr.Location.Col)
}

// CollectEqualityLocs scans a parsed (pre-compilation) module and returns the
// source locations of all == expressions. OPA compilation collapses =, ==, and
// := into the same "eq" operator, so these locations are the only way to
// distinguish pure equality checks from assignments in the compiled AST.
func CollectEqualityLocs(mod *ast.Module) map[string]bool {
	locs := make(map[string]bool)
	for _, rule := range mod.Rules {
		ast.WalkExprs(rule, func(e *ast.Expr) bool {
			if terms, ok := e.Terms.([]*ast.Term); ok && len(terms) > 0 &&
				terms[0].String() == "equal" && e.Location != nil {
				locs[exprLocKey(e)] = true
			}
			return false
		})
	}
	return locs
}
