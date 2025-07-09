package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
)

func (t *Translator) exprToSmt(expr ast.Expr) error {

	return nil
}

// termToSmt converts a Rego AST term to its SMT-LIB string representation.
//
// Parameters:
//
//	term *ast.Term: The Rego AST term to convert.
//
// Returns:
//
//	string: The SMT-LIB string representation of the term.
//	error: An error if the term cannot be converted.
func (t *Translator) termToSmt(term *ast.Term) (string, error) {
	switch v := term.Value.(type) {
	case ast.String:
		// Convert Rego string to SMT-LIB string literal
		return "\"" + string(v) + "\"", nil
	case ast.Number:
		// Convert Rego number to SMT-LIB numeral
		return v.String(), nil
	case ast.Boolean:
		if bool(v) {
			return "true", nil
		}
		return "false", nil
	case *ast.Array:
		// Convert array to SMT-LIB (as a sequence)
		return "", verr.ErrExplicitArraysNotSupported
	case ast.Object:
		// Not directly supported in SMT-LIB, return error
		return "", verr.ErrObjectConversionNotSupported
	case ast.Set:
		// Not directly supported in SMT-LIB, return error
		return "", verr.ErrSetConversionNotSupported
	case *ast.Var:
		// Variable name
		return v.String(), nil
	case ast.Call:
		// Handle string functions and other builtins
		op := v[0].String()
		args := make([]string, len(v)-1)
		for i := 1; i < len(v); i++ {
			s, err := t.termToSmt(v[i])
			if err != nil {
				return "", err
			}
			args[i-1] = s
		}
		return regoFuncToSmt(op, args)
	default:
		return "", fmt.Errorf("%w: %T", verr.ErrUnsupportedTermType, v)
	}
}

// regoFuncToSmt converts a Rego function/operator name and its arguments to an SMT-LIB function application string.
//
// Parameters:
//
//	op string: The Rego function/operator name.
//	args []string: The arguments to the function/operator as SMT-LIB strings.
//
// Returns:
//
//	string: The SMT-LIB function application string.
//	error: An error if the function/operator is not supported.
func regoFuncToSmt(op string, args []string) (string, error) {
	// Map of rego function/operator names to SMT-LIB function names
	funcMap := map[string]string{
		"plus":       "+",
		"minus":      "-",
		"mul":        "*",
		"div":        "div",
		"eq":         "=",
		"concat":     "str.++",
		"contains":   "str.contains",
		"startswith": "str.prefixof",
		"endswith":   "str.suffixof",
		"length":     "str.len",
		"indexof":    "str.indexof",
		"substring":  "str.substr",
	}

	if op == "neq" {
		return "(not (= " + strings.Join(args, " ") + "))", nil
	}

	if smtFunc, ok := funcMap[op]; ok {
		return fmt.Sprintf("(%s %s)", smtFunc, strings.Join(args, " ")), nil
	}
	return "", fmt.Errorf("%w: %s", verr.ErrUnsupportedFunction, op)
}
