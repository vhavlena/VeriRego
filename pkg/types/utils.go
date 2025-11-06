package types

import (
	"github.com/open-policy-agent/opa/ast"
)

// isVar reports whether the provided AST term's value is a variable
// (i.e. an `ast.Var`).
//
// Parameters:
//
//	term *ast.Term: the term to inspect. The function expects a non-nil
//	term whose Value is valid for a type assertion.
//
// Returns:
//
//	bool: true when the term's Value holds an `ast.Var`, false otherwise.
//
// Note: the function performs a type assertion on term.Value and will panic
// if `term` is nil. Callers should ensure `term` is non-nil.
func isVar(term *ast.Term) bool {
	_, c := term.Value.(ast.Var)
	return c
}
