package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
)

// ExprTranslator handles the translation of Rego expressions to SMT-LIB format.
type ExprTranslator struct {
	TypeTrans *TypeTranslator // Type definitions and type-related operations
	context   *TransContext   // Context to collect generated SMT declarations, assertions, and variable mappings
}

// NewExprTranslator creates a new ExprTranslator instance.
func NewExprTranslator(typeTrans *TypeTranslator) *ExprTranslator {
	return &ExprTranslator{
		TypeTrans: typeTrans,
		context:   NewTransContext(),
	}
}

func NewExprTranslatorWithVarMap(typeTrans *TypeTranslator, varMap map[string]string) *ExprTranslator {
	return &ExprTranslator{
		TypeTrans: typeTrans,
		context:   NewTransContextWithVarMap(varMap),
	}
}

// GetTransContext returns the current translation context used by the
// ExprTranslator.
//
// Returns:
//
//	*TransContext: The current translation context containing collected
//	SMT declarations, assertions, and variable mappings created during
//	translation.
func (et *ExprTranslator) GetTransContext() *TransContext {
	return et.context
}

// ClearTransContext resets the translator's translation context to a
// fresh TransContext, discarding any previously collected declarations,
// assertions, and variable mappings.
func (et *ExprTranslator) ClearTransContext() {
	et.context = NewTransContext()
}

// ExprToSmt converts a Rego AST expression to its SMT-LIB string representation.
//
// Parameters:
//
//	expr *ast.Expr: The Rego AST expression to convert.
//
// Returns:
//
//	string: The SMT-LIB string representation of the expression.
//	error: An error if the expression cannot be converted.
func (et *ExprTranslator) ExprToSmt(expr *ast.Expr) (string, error) {
	// If the expression is a single term, just convert it
	if term, ok := expr.Terms.(*ast.Term); ok {
		smtStr, err := et.termToSmt(term)
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
		argStr, err := et.termToSmt(terms[i])
		if err != nil {
			return "", err
		}
		args[i-1] = argStr
	}

	// Use regoFuncToSmt to get the SMT-LIB string for the operator
	smtStr, err := et.regoFuncToSmt(opStr, args, terms)
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
func (et *ExprTranslator) termToSmt(term *ast.Term) (string, error) {
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
		return et.explicitArrayToSmt(v)
	case ast.Object:
		return et.handleConstObject(v)
	case ast.Set:
		// Not directly supported in SMT-LIB, return error
		return "", verr.ErrSetConversionNotSupported
	case ast.Var:
		// Variable name
		return v.String(), nil
	case ast.Ref:
		return et.refToSmt(v)
	case ast.Call:
		// Handle string functions and other builtins
		op := removeQuotes(v[0].String())
		args := make([]string, len(v)-1)
		for i := 1; i < len(v); i++ {
			s, err := et.termToSmt(v[i])
			if err != nil {
				return "", err
			}
			args[i-1] = s
		}
		return et.regoFuncToSmt(op, args, v)
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
func (et *ExprTranslator) regoFuncToSmt(op string, args []string, terms []*ast.Term) (string, error) {
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

	funcName := et.TypeTrans.getFreshVariable(op, et.context.VarMap)
	if err := et.declareUnintFunc(funcName, terms); err != nil {
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
func (et *ExprTranslator) refToSmt(ref ast.Ref) (string, error) {
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
		tp, ok := et.TypeTrans.TypeInfo.Types[baseVar]
		if !ok {
			return "", verr.ErrTypeNotFound
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
func (et *ExprTranslator) explicitArrayToSmt(arr *ast.Array) (string, error) {
	varName := et.TypeTrans.getFreshVariable("const_arr", et.context.VarMap)
	termStr := arr.String()
	tp, ok := et.TypeTrans.TypeInfo.Types[termStr]
	if !ok {
		return "", verr.ErrTypeNotFound
	}
	varDecl, err := et.TypeTrans.getVarDeclaration(varName, &tp)
	if err != nil {
		return "", err
	}
	// store the variable in VarMap to store the fresh variable name
	et.context.VarMap[termStr] = varName
	varAssert, err := et.TypeTrans.getSmtConstrAssert(varName, &tp)
	if err != nil {
		return "", err
	}
	et.context.Bucket.Decls = append(et.context.Bucket.Decls, varDecl)
	et.context.Bucket.Asserts = append(et.context.Bucket.Asserts, varAssert)

	for i := 0; i < arr.Len(); i++ {
		elem := arr.Elem(i)
		elemSmt, err := et.termToSmt(elem)
		if err != nil {
			return "", err
		}
		smtAssert := fmt.Sprintf("(assert (= (select (arr %s) %d) %s))", varName, i, elemSmt)
		et.context.Bucket.Asserts = append(et.context.Bucket.Asserts, smtAssert)
	}

	return varName, nil
}

// declareUnintFunc declares an uninterpreted function in SMT-LIB format based on the function name and the types of its parameters and return value.
//
// Parameters:
//
//	name string: The name of the function to declare.
//	terms []*ast.Term: The terms representing the function/operator and its arguments. The types are inferred from et.TypeTrans.TypeInfo.
//
// Returns:
//
//	error: An error if type information for any term is missing.
func (et *ExprTranslator) declareUnintFunc(name string, terms []*ast.Term) error {
	// gather parameter types
	pars := make([]string, len(terms)-1)
	for i := 1; i < len(terms); i++ {
		tp, ok := et.TypeTrans.TypeInfo.Types[terms[i].String()]
		if !ok {
			return verr.ErrTypeNotFound
		}
		pars[i-1] = et.TypeTrans.getSmtType(&tp)
	}
	// gather return type
	rtype, ok := et.TypeTrans.TypeInfo.Types[terms[0].String()]
	if !ok {
		return verr.ErrTypeNotFound
	}

	decls := fmt.Sprintf("(declare-fun %s (%s) %s)", name, strings.Join(pars, " "), et.TypeTrans.getSmtType(&rtype))
	et.context.Bucket.Decls = append(et.context.Bucket.Decls, decls)
	return nil
}

// handleConstObject converts a Rego constant object to an SMT-LIB variable, adds its declaration and assertion, and returns the variable name.
//
// Parameters:
//
//	obj ast.Object: The Rego object to convert.
//
// Returns:
//
//	string: The SMT-LIB variable name representing the object.
//	error: An error if type information is missing or conversion fails.
func (et *ExprTranslator) handleConstObject(obj ast.Object) (string, error) {
	varName := et.TypeTrans.getFreshVariable("const_obj", et.context.VarMap)
	tp, ok := et.TypeTrans.TypeInfo.Types[obj.String()]
	if !ok {
		return "", verr.ErrTypeNotFound
	}

	decl, err := et.TypeTrans.getVarDeclaration(varName, &tp)
	if err != nil {
		return "", err
	}
	et.context.Bucket.Decls = append(et.context.Bucket.Decls, decl)

	smtConstr, er := et.TypeTrans.getSmtConstrAssert(varName, &tp)
	if er != nil {
		return "", er
	}
	et.context.Bucket.Asserts = append(et.context.Bucket.Asserts, smtConstr)

	return varName, nil
}
