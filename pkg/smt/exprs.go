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
	case ast.Ref:
		return t.refToSmt(v)
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

// refToSmt converts a Rego reference (ast.Ref) to its SMT-LIB string representation.
//
// Parameters:
//
//	ref ast.Ref: The Rego reference to convert.
//
// Returns:
//
//	string: The SMT-LIB string representation of the reference.
//	error: An error if the reference cannot be converted.
func (t *Translator) refToSmt(ref ast.Ref) (string, error) {
	if len(ref) == 0 {
		return "", verr.ErrEmptyReferenceConv
	}

	head := ref[0].Value.String()
	// input prefix
	if head == "input" {

		var baseVar string
		var path []string

		// Check for input.parameters.<name>
		if len(ref) >= 3 {
			second := ref[1].Value.String()
			if second == "\"parameters\"" {
				baseVar = getParamVar(ref)
				path = refToPath(ref[3:])
			} else {
				path = refToPath(ref[4:])
				baseVar = getSchemaVar(ref)
			}
		}
		fmt.Printf("Debug: baseVar: %s, path: %v\n", baseVar, path)
		tp, ok := t.TypeInfo.Types[baseVar]
		if !ok {
			return "", verr.ErrSchemaVarTypeNotFound
		}
		smt, err := getSmtRef(baseVar, path, &tp)
		if err != nil {
			return "", fmt.Errorf("error converting reference to SMT: %w", err)
		}
		return smt, nil
	}

	// TODO: handle most general references
	return ref.String(), nil
}
