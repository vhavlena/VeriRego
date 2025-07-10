package smt

import (
	"fmt"
	"math/rand"
	"strings"
	"time"

	"github.com/open-policy-agent/opa/ast"

	"github.com/vhavlena/verirego/pkg/err"
	"github.com/vhavlena/verirego/pkg/types"
)

const letterBytes = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

func RandString(n int) string {
	rand.Seed(time.Now().UnixNano())
	b := make([]byte, n)
	for i := range b {
		b[i] = letterBytes[rand.Intn(len(letterBytes))]
	}
	return string(b)
}

// GenerateTypeDefs generates SMT-LIB datatype and sort declarations, variable declarations, and constraints for all variables.
//
// It determines the maximum type depth, generates the necessary SMT-LIB type and sort definitions,
// declares each variable, and asserts the SMT constraints for each variable according to its type.
// The generated lines are appended to the Translator's smtLines field.
//
// Returns:
//
//	error: An error if any variable declaration or constraint generation fails.
func (t *Translator) GenerateTypeDefs(globalVars map[string]any) error {
	datatypes := t.getDatatypesDeclaration()
	t.smtLines = append(t.smtLines, datatypes...)

	maxDepth := 0
	vars := make([]string, 0, len(t.TypeInfo.Types))
	for name, tp := range t.TypeInfo.Types {
		if _, ok := globalVars[name]; !ok {
			continue
		}
		_, ok := t.TypeInfo.Refs[name].(ast.Var)
		if ok {
			vars = append(vars, name)
			maxDepth = max(maxDepth, tp.TypeDepth())
		}
	}
	sortDefs := t.getSortDefinitions(maxDepth)
	t.smtLines = append(t.smtLines, sortDefs...)

	for _, name := range vars {
		tp := t.TypeInfo.Types[name]
		smtVar, er := getVarDeclaration(name, &tp)
		if er != nil {
			return er
		}
		t.smtLines = append(t.smtLines, smtVar)
	}

	for _, name := range vars {
		tp := t.TypeInfo.Types[name]
		smtConstr, er := t.getSmtConstrAssert(name, &tp)
		if er != nil {
			return er
		}
		t.smtLines = append(t.smtLines, smtConstr)
	}

	return nil
}

// getTypeConstr returns the SMT type constraint function name for a given Rego type.
//
// Parameters:
//
//	tp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	string: The SMT type constraint function name.
func getTypeConstr(tp *types.RegoTypeDef) string {
	if tp.IsAtomic() {
		return "is-Atom"
	} else if tp.IsArray() {
		return "is-OArray"
	}
	return "is-OObj"
}

// getDatatypesDeclaration returns SMT-LIB datatype declarations for the supported types.
//
// Returns:
//
//	[]string: A slice of SMT-LIB datatype declaration strings.
func (t *Translator) getDatatypesDeclaration() []string {
	oatom := `
(declare-datatypes ()
	((OAtom
		(OString (str String))
		(ONumber (num Int))
		(OBoolean (bool Bool))
		ONull
	))
)`
	ogentype := `
(declare-datatypes (T)
	((OGenType
		(Atom (atom OAtom))
		(OObj (obj (Array String T)))
		(OArray (arr (Array Int T)))
	))
)`
	gettypeatom := `
(declare-datatypes ()
  ((OGenTypeAtom (Atom (atom OAtom)) ))
)`
	return []string{oatom, ogentype, gettypeatom}
}

// getVarDeclaration returns the SMT-LIB variable declaration for a given variable name and type.
//
// Parameters:
//
//	name string: The variable name.
//	tp *types.RegoTypeDef: The Rego type definition for the variable.
//
// Returns:
//
//	string: The SMT-LIB variable declaration string.
//	error: An error if the declaration could not be generated.
func getVarDeclaration(name string, tp *types.RegoTypeDef) (string, error) {
	return fmt.Sprintf("(declare-fun %s () OTypeD%d)", name, tp.TypeDepth()), nil
}

// getSortDefinitions returns SMT-LIB sort definitions up to the given maximum depth.
//
// Parameters:
//
//	maxDepth int: The maximum depth for sort definitions.
//
// Returns:
//
//	[]string: A slice of SMT-LIB sort definition strings.
func (t *Translator) getSortDefinitions(maxDepth int) []string {
	defs := make([]string, 0, maxDepth+1)
	for i := 0; i <= maxDepth; i++ {
		if i == 0 {
			defs = append(defs, "(define-sort OTypeD0 () (OGenType OGenTypeAtom))")
			continue
		}
		defs = append(defs, fmt.Sprintf("(define-sort OTypeD%d () (OGenType OTypeD%d))", i, i-1))
	}
	return defs
}

// getSmtConstrAssert generates an SMT-LIB assertion for the constraints of a value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	string: The SMT-LIB assertion string.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtConstrAssert(smtValue string, tp *types.RegoTypeDef) (string, error) {
	andArr, er := t.getSmtConstr(smtValue, tp)
	if er != nil {
		return "", err.ErrSmtConstraints(er)
	}
	assert := strings.Join(andArr, " ")
	return fmt.Sprintf("(assert (and %s))", assert), nil
}

// getSmtConstr generates SMT-LIB constraints for a value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	[]string: A slice of SMT-LIB constraint strings.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if tp.IsAtomic() {
		return t.getSmtAtomConstr(smtValue, tp)
	} else if tp.IsObject() {
		return t.getSmtObjectConstr(smtValue, tp)
	} else if tp.IsArray() {
		return t.getSmtArrConstr(smtValue, tp)
	}
	return nil, err.ErrUnsupportedType
}

// getSmtObjectConstr generates SMT-LIB constraints for an object value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego object type definition.
//
// Returns:
//
//	[]string: A slice of SMT-LIB constraint strings for the object fields.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtObjectConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsObject() {
		return nil, err.ErrUnsupportedType
	}

	andConstr := make([]string, 0, 64)
	for key, val := range tp.ObjectFields {
		sel := fmt.Sprintf("(select (obj %s) \"%s\")", smtValue, key)
		if !val.IsAtomic() {
			andConstr = append(andConstr, fmt.Sprintf("(%s %s)", getTypeConstr(&val), sel))
		}

		valAnalysis, er := t.getSmtConstr(sel, &val)
		if er != nil {
			return nil, err.ErrSmtFieldConstraints(key, er)
		}
		andConstr = append(andConstr, valAnalysis...)
	}
	return andConstr, nil
}

// getSmtAtomConstr generates SMT-LIB constraints for an atomic value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego atomic type definition.
//
// Returns:
//
//	[]string: A slice with a single SMT-LIB constraint string for the atomic value.
//	error: An error if the atomic type is unsupported.
func (t *Translator) getSmtAtomConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsAtomic() {
		return nil, err.ErrUnsupportedType
	}

	switch tp.AtomicType {
	case types.AtomicString:
		return []string{fmt.Sprintf("(is-OString (atom %s))", smtValue)}, nil
	case types.AtomicInt:
		return []string{fmt.Sprintf("(is-ONumber (atom %s))", smtValue)}, nil
	case types.AtomicBoolean:
		return []string{fmt.Sprintf("(is-OBoolean (atom %s))", smtValue)}, nil
	default:
		return nil, err.ErrUnsupportedAtomic
	}
}

// getSmtArrConstr generates SMT-LIB constraints for an array value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego array type definition.
//
// Returns:
//
//	[]string: A slice of SMT-LIB constraint strings for the array and its elements.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtArrConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsArray() {
		return nil, err.ErrUnsupportedType
	}
	andConstr := make([]string, 0, 64)
	andConstr = append(andConstr, fmt.Sprintf("(is-OArray %s)", smtValue))

	valAnalysis, er := t.getSmtConstr("elem", tp.ArrayType)
	if er != nil {
		return nil, er
	}
	ands := fmt.Sprintf("(and %s)", strings.Join(valAnalysis, " "))
	qvar := RandString(5)
	forall := fmt.Sprintf("(forall ((%s Int))  (let ((elem (select (arr %s) %s))) %s))", qvar, smtValue, qvar, ands)
	andConstr = append(andConstr, forall)

	return andConstr, nil
}

func getSmtRef(smtvar string, path []string, tp *types.RegoTypeDef) (string, error) {
	smtref := smtvar
	actType := tp
	for _, p := range path {
		if !actType.IsObject() {
			return "", fmt.Errorf("only object types can be used in references")
		}
		val := actType.ObjectFields[p]
		actType = &val
		smtref = fmt.Sprintf("(select (obj %s) \"%s\")", smtref, p)
	}
	return smtref, nil
}

// refToPath converts a Rego AST reference to a slice of strings representing the path.
//
// Parameters:
//
//	ref ast.Ref: The reference to convert.
//
// Returns:
//
//	[]string: The path as a slice of strings.
func refToPath(ref ast.Ref) []string {
	path := make([]string, 0, len(ref))
	for _, term := range ref {
		if str, ok := term.Value.(ast.String); ok {
			path = append(path, string(str))
		} else {
			path = append(path, term.String())
		}
	}
	return path
}

// removeQuotes removes leading and trailing double quotes from a string, if present.
//
// Parameters:
//
//	s string: The input string.
//
// Returns:
//
//	string: The string without leading and trailing quotes.
func removeQuotes(s string) string {
	if len(s) < 2 {
		return s
	}
	if s[0] == '"' && s[len(s)-1] == '"' {
		return s[1 : len(s)-1]
	}
	return s
}

// getSchemaVar constructs a schema variable name from a Rego reference for input.review.object.<name>.
//
// Parameters:
//
//	ref ast.Ref: The reference to convert.
//
// Returns:
//
//	string: The schema variable name as a dot-separated string.
func getSchemaVar(ref ast.Ref) string {
	// input.review.object.<name>
	return fmt.Sprintf("%s.%s.%s.%s", removeQuotes(ref[0].String()), removeQuotes(ref[1].String()), removeQuotes(ref[2].String()), removeQuotes(ref[3].String()))
}

// getParamVar constructs a parameter variable name from a Rego reference for input.parameters.<name>.
//
// Parameters:
//
//	ref ast.Ref: The reference to convert.
//
// Returns:
//
//	string: The parameter variable name as a dot-separated string.
func getParamVar(ref ast.Ref) string {
	// input.parameters.<name>
	return fmt.Sprintf("%s.%s.%s", removeQuotes(ref[0].String()), removeQuotes(ref[1].String()), removeQuotes(ref[2].String()))
}
