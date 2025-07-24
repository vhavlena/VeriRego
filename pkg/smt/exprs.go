package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
)

// exprToSmt converts a Rego AST expression to its SMT-LIB string representation.
//
// Parameters:
//
//	expr *ast.Expr: The Rego AST expression to convert.
//
// Returns:
//
//	string: The SMT-LIB string representation of the expression.
//	error: An error if the expression cannot be converted.
func (t *Translator) exprToSmt(expr *ast.Expr) (string, error) {
	// If the expression is a single term, just convert it
	if term, ok := expr.Terms.(*ast.Term); ok {
		smtStr, err := t.termToSmt(term)
		if err != nil {
			return "", err
		}
		return smtStr, nil
	}

	// If the expression is a call or operator (e.g., [op, arg1, arg2, ...])
	terms, ok := expr.Terms.([]*ast.Term)
	if !ok || len(terms) == 0 {
		return "", verr.ErrInvalidEmptyTerm
	}

	opStr := removeQuotes(terms[0].String())

	// Convert all arguments
	args := make([]string, len(terms)-1)
	for i := 1; i < len(terms); i++ {
		argStr, err := t.termToSmt(terms[i])
		if err != nil {
			return "", err
		}
		args[i-1] = argStr
	}

	// Use regoFuncToSmt to get the SMT-LIB string for the operator
	smtStr, err := t.regoFuncToSmt(opStr, args, terms)
	if err != nil {
		return "", err
	}

	return smtStr, nil
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
		// convert to a fresh variable with the array type
		return t.explicitArrayToSmt(v)
	case ast.Object:
		// Not directly supported in SMT-LIB, return error
		return "", verr.ErrObjectConversionNotSupported
	case ast.Set:
		// Not directly supported in SMT-LIB, return error
		return "", verr.ErrSetConversionNotSupported
	case ast.Var:
		// Variable name
		return v.String(), nil
	case ast.Ref:
		return t.refToSmt(v)
	case ast.Call:
		// Handle string functions and other builtins
		op := removeQuotes(v[0].String())
		args := make([]string, len(v)-1)
		for i := 1; i < len(v); i++ {
			s, err := t.termToSmt(v[i])
			if err != nil {
				return "", err
			}
			args[i-1] = s
		}
		return t.regoFuncToSmt(op, args, v)
	default:
		return "", fmt.Errorf("%w: %T", verr.ErrUnsupportedTermType, v)
	}
}

// regoFuncToSmt converts a Rego function/operator name and its arguments to an SMT-LIB function application string.
// If the operator is a known built-in, it maps to the corresponding SMT-LIB function. Otherwise, it declares an uninterpreted function
// with the appropriate parameter and return types (using declareUnintFunc) and returns its application.
//
// Parameters:
//
//	op string: The Rego function/operator name.
//	args []string: The arguments to the function/operator as SMT-LIB strings.
//	terms []*ast.Term: The terms representing the operator and its arguments, used for type inference.
//
// Returns:
//
//	string: The SMT-LIB function application string.
//	error: An error if the function/operator is not supported or type information is missing.
func (t *Translator) regoFuncToSmt(op string, args []string, terms []*ast.Term) (string, error) {
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
		"equal":      "=",
		"gt":         ">",
		"lt":         "<",
	}

	if op == "neq" {
		return "(not (= " + strings.Join(args, " ") + "))", nil
	}

	if smtFunc, ok := funcMap[op]; ok {
		return fmt.Sprintf("(%s %s)", smtFunc, strings.Join(args, " ")), nil
	}

	funcName := t.getFreshVariable(op)
	if err := t.declareUnintFunc(funcName, terms); err != nil {
		return "", err
	}

	return fmt.Sprintf("(%s %s)", funcName, strings.Join(args, " ")), nil
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

// explicitArrayToSmt converts an explicit Rego array to an SMT-LIB variable and adds its declaration and assertion.
//
// Parameters:
//
//	arr *ast.Array: The Rego array to convert.
//
// Returns:
//
//	string: The SMT-LIB variable name representing the array.
//	error: An error if the type information is missing or conversion fails.
func (t *Translator) explicitArrayToSmt(arr *ast.Array) (string, error) {
	varName := t.getFreshVariable("const_arr")
	termStr := arr.String()
	tp, ok := t.TypeInfo.Types[termStr]
	if !ok {
		return "", verr.ErrSchemaVarTypeNotFound
	}
	varDecl, err := getVarDeclaration(varName, &tp)
	if err != nil {
		return "", err
	}
	// store the variable in VarMap to store the fresh variable name
	t.VarMap[termStr] = varName
	varAssert, err := t.getSmtConstrAssert(varName, &tp)
	if err != nil {
		return "", err
	}
	t.smtDecls = append(t.smtDecls, varDecl)
	t.smtAsserts = append(t.smtAsserts, varAssert)

	for i := 0; i < arr.Len(); i++ {
		elem := arr.Elem(i)
		elemSmt, err := t.termToSmt(elem)
		if err != nil {
			return "", err
		}
		smtAssert := fmt.Sprintf("(assert (= (select (arr %s) %d) %s))", varName, i, elemSmt)
		t.smtAsserts = append(t.smtAsserts, smtAssert)
	}

	return varName, nil
}

// declareUnintFunc declares an uninterpreted function in SMT-LIB format based on the function name and the types of its parameters and return value.
//
// Parameters:
//
//	name string: The name of the function to declare.
//	terms []*ast.Term: The terms representing the function/operator and its arguments. The types are inferred from t.TypeInfo.
//
// Returns:
//
//	error: An error if type information for any term is missing.
func (t *Translator) declareUnintFunc(name string, terms []*ast.Term) error {
	// gather parameter types
	pars := make([]string, len(terms)-1)
	for i := 1; i < len(terms); i++ {
		tp, ok := t.TypeInfo.Types[terms[i].String()]
		if !ok {
			return fmt.Errorf("type information not found for term: %s", terms[i].String())
		}
		pars[i-1] = getSmtType(&tp)
	}
	// gather return type
	rtype, ok := t.TypeInfo.Types[terms[0].String()]
	if !ok {
		return fmt.Errorf("type information not found for term: %s", terms[0].String())
	}

	decls := fmt.Sprintf("(declare-fun %s (%s) %s)", name, strings.Join(pars, " "), getSmtType(&rtype))
	t.smtDecls = append(t.smtDecls, decls)
	return nil
}
