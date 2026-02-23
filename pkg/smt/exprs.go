package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
	"github.com/vhavlena/verirego/pkg/types"
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

func (et *ExprTranslator) BodyToSmt(ruleBody *ast.Body) (*SmtProposition,map[string]SmtValue,error) {
	bodySmts := make([]SmtProposition, 0, len(*ruleBody))
	localVarDefs := make(map[string]SmtValue, 0)
	for _, expr := range *ruleBody {
		// single term
		if term, ok := expr.Terms.(*ast.Term); ok {
			smtVal,err := et.termToSmtValue(term)
			if err != nil {
				return nil, localVarDefs, err
			}
			bodySmts = append(bodySmts, *smtVal.Holds())
			continue
		}

		// call
		terms, ok := expr.Terms.([]*ast.Term)
		if !ok || len(terms) == 0 {
			return nil, localVarDefs, verr.ErrInvalidEmptyTerm
		}

		opStr := removeQuotes(terms[0].String())
		
		// check if it is assigning
		isAssigning := false
		if opStr == ast.Equality.Name {
			if name,ok := terms[1].Value.(ast.Var); ok {
				// create variable
				rhs := terms[2]
				val,err := et.termToSmtValue(rhs)
				if err != nil {
					return nil, localVarDefs, err
				}

				localVarDefs[removeQuotes(name.String())] = *val
				isAssigning = true
			}
		}
		op,err := getOperation(opStr)
		if err != nil {
			return nil, localVarDefs, err
		}
		
		arity := op.Decl.Arity()
		params := len(terms)-1
		if arity < params {		// the return is a part of the call
			if name,ok := terms[params].Value.(ast.Var); ok {	// creating variable
				// remove assigned variable from call
				rhs := terms[0:len(terms)-1]
				args := make([]string, len(rhs)-1)
				for i := 1; i < len(rhs); i++ {
					s, err := et.termToSmt(terms[i])
					if err != nil {
						return nil, localVarDefs, err
					}
					args[i-1] = s
				}
				val,err := et.getOperationValue(opStr,args,rhs)
				if err != nil {
					return nil, localVarDefs, err
				}

				localVarDefs[removeQuotes(name.String())] = *val
				isAssigning = true
			}
		}
		if isAssigning {	// if expression introduced a local variable, it does not hold any value
			continue
		}

		// Convert all arguments
		args := make([]string, len(terms)-1)
		for i := 1; i < len(terms); i++ {
			argStr, err := et.termToSmt(terms[i])
			if err != nil {
				return nil, localVarDefs, err
			}
			args[i-1] = argStr
		}

		// Use regoFuncToSmt to get the SMT-LIB string for the operator
		bodySmt, err := et.getOperationValue(opStr, args, terms)
		if err != nil {
			return nil, localVarDefs, err
		}
		bodySmts = append(bodySmts, *bodySmt.Holds())
	}

	bodySmt := And(bodySmts)
	return bodySmt, localVarDefs, nil
}

func (et *ExprTranslator) getOperationValue(op string, args []string, rhs []*ast.Term) (*SmtValue, error) {
	val,err := et.regoFuncToSmt(op,args,rhs)
	if err != nil {
		return nil, err
	}
	construct, err := getAtomConstructorForOperation(op)
	if err != nil {
		return nil, err
	}
	if construct != "" {
		val = fmt.Sprintf("(%s %s)", construct, val)
	}
	return NewSmtValue(val, 0), nil	// TODO: user-defined functions
}

func getOperation(op string) (*ast.Builtin,error) {
	switch op {
	case ast.Plus.Name:
		return ast.Plus,nil
	case ast.Minus.Name:
		return ast.Minus,nil
	case ast.Multiply.Name:
		return ast.Multiply,nil
	case ast.Divide.Name:
		return ast.Divide,nil
	case ast.Equal.Name:
		return ast.Equal,nil
	case ast.Equality.Name:
		return ast.Equality,nil
	case ast.Assign.Name:
		return ast.Assign,nil
	case ast.GreaterThan.Name:
		return ast.GreaterThan,nil
	case ast.GreaterThanEq.Name:
		return ast.GreaterThanEq,nil
	case ast.LessThan.Name:
		return ast.LessThan,nil
	case ast.LessThanEq.Name:
		return ast.LessThanEq,nil
	case ast.Concat.Name:
		return ast.Concat,nil
	case ast.Contains.Name:
		return ast.Contains,nil
	case ast.StartsWith.Name:
		return ast.StartsWith,nil
	case ast.EndsWith.Name:
		return ast.EndsWith,nil
	case ast.IndexOf.Name:
		return ast.IndexOf,nil
	case ast.Substring.Name:
		return ast.Substring,nil
	default:
		return nil,verr.ErrUnsupportedFunction
	}
}

func /*(et *ExprTranslator)*/ getOperationReturnType(opName string) (types.AtomicType,error) {
	funcMap := map[string]types.AtomicType{
		ast.Plus.Name:          types.AtomicInt,        // +
		ast.Minus.Name:         types.AtomicInt,        // -
		ast.Multiply.Name:      types.AtomicInt,        // *
		ast.Divide.Name:        types.AtomicInt,        // /
		ast.Equal.Name:         types.AtomicBoolean,    // ==
		ast.Equality.Name:      types.AtomicBoolean,    // =
		ast.Assign.Name:        types.AtomicBoolean,    // :=
		ast.GreaterThan.Name:   types.AtomicBoolean,    // >
		ast.GreaterThanEq.Name:	types.AtomicBoolean,    // >=
		ast.LessThan.Name:      types.AtomicBoolean,    // <
		ast.LessThanEq.Name:    types.AtomicBoolean,    // <=
		ast.Concat.Name:        types.AtomicString,     // concat
		ast.Contains.Name:      types.AtomicBoolean,    // contains
		ast.StartsWith.Name:    types.AtomicBoolean,    // startswith
		ast.EndsWith.Name:      types.AtomicBoolean,    // endswith
		ast.IndexOf.Name:       types.AtomicInt,        // indexof
		ast.Substring.Name:     types.AtomicString,     // substring
		// "length" does not exist
	}

	// TODO: user defined functions
	if atomicType,found := funcMap[opName]; found {
		return atomicType,nil
	}
	return types.AtomicUndef,verr.ErrUnsupportedFunction
}

func getAtomConstructorForOperation(op string) (string,error) {
	opType,err := getOperationReturnType(op)
	if err != nil {
		return "",verr.ErrUnsupportedFunction
	}
	return getAtomConstructorFromType(opType),nil
}

func getAtomConstructorFromType(t types.AtomicType) string {
	switch t {
	case types.AtomicString:
		return "OString"
	case types.AtomicInt:
		return "ONumber"
	case types.AtomicBoolean:
		return "OBoolean"
	default:
		return ""
	}
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
		return et.TypeTrans.getVarValue(v.String())
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

func (et *ExprTranslator) termToSmtValue(term *ast.Term) (*SmtValue, error) {
	switch v := term.Value.(type) {
	case ast.String:
		return NewSmtValueFromString(string(v)), nil
	case ast.Number:
		if val,ok := v.Int(); ok {
			return NewSmtValueFromInt(val), nil
		}
		return nil,verr.ErrUnsupportedAtomic
	case ast.Boolean:
		return NewSmtValueFromBoolean(bool(v)), nil
	case *ast.Array:
		return et.arrayToSmt(v)
	case ast.Object:
		return et.objectToSmt(v)
	case ast.Set:
		// Not directly supported in SMT-LIB, return error
		return nil, verr.ErrSetConversionNotSupported
	case ast.Var:
		return et.GetVarValue(v)
	case ast.Ref:
		name := removeQuotes(v[len(v)-1].String())
		tp, ok := et.TypeTrans.TypeInfo.Types[name]
		if !ok {
			return nil, verr.ErrTypeNotFound
		}
		return NewSmtValue(name, tp.TypeDepth()), nil
	case ast.Call:
		// Handle string functions and other builtins
		op := removeQuotes(v[0].String())
		args := make([]string, len(v)-1)
		for i := 1; i < len(v); i++ {
			s, err := et.termToSmt(v[i])
			if err != nil {
				return nil, err
			}
			args[i-1] = s
		}
		val, err := et.regoFuncToSmt(op, args, v)
		if err != nil {
			return nil, err
		}
		construct,err := getAtomConstructorForOperation(op)
		if err != nil {
			return nil,err
		}
		if construct != "" {
			val = fmt.Sprintf("(%s %s)", construct, val)
		}
		return NewSmtValue(val, 0), nil	// TODO: built-in functions
	default:
		return nil, fmt.Errorf("%w: %T", verr.ErrUnsupportedTermType, v)
	}
}

func (et *ExprTranslator) GetVarValue(v ast.Var) (*SmtValue, error) {
		name := removeQuotes(v.String())
		tp, ok := et.TypeTrans.TypeInfo.Types[name]
		if !ok {
			return nil, verr.ErrTypeNotFound
		}
		return NewSmtValue(name, tp.TypeDepth()), nil
}

func (et *ExprTranslator) arrayToSmt(arr *ast.Array) (*SmtValue, error) {
	tp, ok := et.TypeTrans.TypeInfo.Types[arr.String()]
	if !ok {
		return nil, verr.ErrTypeNotFound
	}

	depth := tp.TypeDepth()
	arrSmt := createConstArray("Int", depth)

	for index := range arr.Len() {
		val := arr.Elem(index)
		valSmt,err := et.termToSmtValue(val)
		if err != nil {
			return nil,err
		}
		valSmt = valSmt.WrapToDepth(depth-1)
		arrSmt = fmt.Sprintf("(store %s %d %s)", arrSmt, index, valSmt.String())
	}

	return &SmtValue{
		value: fmt.Sprintf("(OArray%d %s)",depth,arrSmt), 
		depth: depth,
	}, nil
}

func (et *ExprTranslator) objectToSmt(obj ast.Object) (*SmtValue, error) {
	tp, ok := et.TypeTrans.TypeInfo.Types[obj.String()]
	if !ok {
		return nil, verr.ErrTypeNotFound
	}

	depth := tp.TypeDepth()
	objSmt := createConstArray("String", depth)

	for _, key := range obj.Keys() {
		keyStr := removeQuotes(key.String())
		val := obj.Get(key)
		valSmt,err := et.termToSmtValue(val)
		if err != nil {
			return nil,err
		}
		valSmt = valSmt.WrapToDepth(depth-1)
		objSmt = fmt.Sprintf("(store %s %s %s)", objSmt, keyStr, valSmt.String())
	}

	return &SmtValue{
		value: fmt.Sprintf("(OObj%d %s)",depth,objSmt),
		depth: depth,
	}, nil
}

func createConstArray(keyType string, depth int) string {
	undefChild := "OUndef"
	for d := range depth-1 {
		undefChild = fmt.Sprintf("(Atom%d %s)",d+1,undefChild)
	}
	return fmt.Sprintf("((as const (Array %s OTypeD%d)) %s)",keyType ,depth-1, undefChild)
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
		smt, actType, err := getSmtRef(baseVar, path, &tp)
		if err != nil {
			return "", fmt.Errorf("error converting reference to SMT: %w", err)
		}
		return et.TypeTrans.getSmtValue(smt, actType)
	}

	// TODO: handle most general references
	return et.TypeTrans.getVarValue(ref.String())
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
	varDeclBucket, err := et.TypeTrans.getVarDeclaration(varName, &tp)
	if err != nil {
		return "", err
	}
	// store the variable in VarMap to store the fresh variable name
	et.context.VarMap[termStr] = varName
	varAssertBucket, err := et.TypeTrans.getSmtConstrAssert(varName, &tp)
	if err != nil {
		return "", err
	}
	et.context.Bucket.Append(varDeclBucket)
	et.context.Bucket.Append(varAssertBucket)

	for i := 0; i < arr.Len(); i++ {
		elem := arr.Elem(i)
		elemSmt, err := et.termToSmt(elem)
		if err != nil {
			return "", err
		}
		depth := max(tp.TypeDepth(), 0)
		eq := RawProposition(fmt.Sprintf("(= (select (arr%d %s) %d) %s)", depth, varName, i, elemSmt))
		et.context.Bucket.Asserts = append(et.context.Bucket.Asserts, Assert(eq))
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

	decl := DeclareFun(name, pars, et.TypeTrans.getSmtType(&rtype))
	et.context.Bucket.Decls = append(et.context.Bucket.Decls, decl)
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

	declBucket, err := et.TypeTrans.getVarDeclaration(varName, &tp)
	if err != nil {
		return "", err
	}
	et.context.Bucket.Append(declBucket)

	smtConstrBucket, er := et.TypeTrans.getSmtConstrAssert(varName, &tp)
	if er != nil {
		return "", er
	}
	et.context.Bucket.Append(smtConstrBucket)

	return varName, nil
}
