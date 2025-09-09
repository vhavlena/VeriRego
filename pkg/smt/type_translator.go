package smt

import (
	"fmt"
	"math/rand"
	"sort"
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

//----------------------------------------------------------------

// TypeTranslator handles SMT type definitions and type-related operations
type TypeTranslator struct {
	TypeInfo *types.TypeAnalyzer // Type information for Rego terms
}

// NewTypeDefs creates a new TypeDefs instance with the given TypeAnalyzer.
func NewTypeDefs(typeInfo *types.TypeAnalyzer) *TypeTranslator {
	return &TypeTranslator{
		TypeInfo: typeInfo,
	}
}

//----------------------------------------------------------------

type Bucket struct {
	TypeDecls []string // SMT type declarations
	Decls     []string // SMT variable declarations
	Asserts   []string // SMT assertions
}

func NewBucket() *Bucket {
	return &Bucket{
		Decls:     make([]string, 0, 64),
		Asserts:   make([]string, 0, 128),
		TypeDecls: make([]string, 0, 32),
	}
}

func (b *Bucket) Append(other *Bucket) {
	b.Decls = append(b.Decls, other.Decls...)
	b.Asserts = append(b.Asserts, other.Asserts...)
	b.TypeDecls = append(b.TypeDecls, other.TypeDecls...)
}

//----------------------------------------------------------------

// GenerateTypeDecls generates SMT-LIB datatype and sort declarations
// required by the types of the variables listed in usedVars.
//
// Parameters:
//
//	usedVars map[string]any: map whose keys are variable names that should be considered.
//
// Returns:
//
//	*Bucket: Bucket containing TypeDecls (datatype and sort definitions).
//	error: An error if generation fails.
func (td *TypeTranslator) GenerateTypeDecls(usedVars map[string]any) (*Bucket, error) {
	bucket := NewBucket()

	datatypes := td.getDatatypesDeclaration()
	bucket.TypeDecls = append(bucket.TypeDecls, datatypes...)

	maxDepth := 0
	for name, tp := range td.TypeInfo.Types {
		if _, ok := usedVars[name]; !ok {
			continue
		}
		maxDepth = max(maxDepth, tp.TypeDepth())
	}
	sortDefs := td.getSortDefinitions(maxDepth)
	bucket.TypeDecls = append(bucket.TypeDecls, sortDefs...)
	return bucket, nil
}

// GenerateVarDecl generates the SMT-LIB declaration and constraint assertion
// for a single variable named varName.
//
// Parameters:
//
//	varName string: The variable name. Must exist in td.TypeInfo.Types.
//
// Returns:
//
//	*Bucket: A Bucket with one entry in Decls (declare-fun) and one in Asserts (constraint assertion).
//	error: An error if generation fails.
func (td *TypeTranslator) GenerateVarDecl(varName string) (*Bucket, error) {
	bucket := NewBucket()
	tp := td.TypeInfo.Types[varName]
	smtVar, er := td.getVarDeclaration(varName, &tp)
	if er != nil {
		return nil, er
	}
	bucket.Decls = append(bucket.Decls, smtVar)

	smtConstr, er := td.getSmtConstrAssert(varName, &tp)
	if er != nil {
		return nil, er
	}
	bucket.Asserts = append(bucket.Asserts, smtConstr)

	return bucket, nil
}

// GenerateVarDecls generates SMT-LIB variable declarations and constraint
// assertions for every variable whose name appears as a key in usedVars.
//
// Parameters:
//
//	usedVars map[string]any: map with variable names to generate declarations for.
//
// Returns:
//
//	*Bucket: Aggregated Bucket of declarations and assertions.
//	error: An error if any generation fails.
func (td *TypeTranslator) GenerateVarDecls(usedVars map[string]any) (*Bucket, error) {
	bucket := NewBucket()
	for name, _ := range usedVars {
		varBucket, er := td.GenerateVarDecl(name)
		if er != nil {
			return nil, er
		}
		bucket.Append(varBucket)
	}
	return bucket, nil
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
func (td *TypeTranslator) getDatatypesDeclaration() []string {
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
func (td *TypeTranslator) getVarDeclaration(name string, tp *types.RegoTypeDef) (string, error) {
	return fmt.Sprintf("(declare-fun %s () %s)", name, td.getSmtType(tp)), nil
}

// getSmtType returns the SMT-LIB sort name for a given Rego type definition based on its type depth.
//
// Parameters:
//
//	ttp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	string: The SMT-LIB sort name corresponding to the type depth.
func (td *TypeTranslator) getSmtType(tp *types.RegoTypeDef) string {
	return fmt.Sprintf("OTypeD%d", tp.TypeDepth())
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
func (td *TypeTranslator) getSortDefinitions(maxDepth int) []string {
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
func (td *TypeTranslator) getSmtConstrAssert(smtValue string, tp *types.RegoTypeDef) (string, error) {
	andArr, er := td.getSmtConstr(smtValue, tp)
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
func (td *TypeTranslator) getSmtConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	switch {
	case tp.IsAtomic():
		return td.getSmtAtomConstr(smtValue, tp)
	case tp.IsObject():
		return td.getSmtObjectConstr(smtValue, tp)
	case tp.IsArray():
		return td.getSmtArrConstr(smtValue, tp)
	case tp.IsUnion():
		return td.getSmtUnionConstr(smtValue, tp)
	default:
		return nil, err.ErrUnsupportedType
	}
}

// getSmtUnionConstr generates SMT-LIB constraints for a union type by combining
// the constraints of each union member with a logical 'or'.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego union type definition.
//
// Returns:
//
//	[]string: A slice containing a single SMT-LIB 'or' expression that
//		combines member constraints, or an empty slice on error.
//	error: An error if any member constraint generation fails or if the
//		type is not a union.

func (td *TypeTranslator) getSmtUnionConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsUnion() {
		return nil, err.ErrUnsupportedType
	}

	orConstr := make([]string, 0, 64)
	for _, member := range tp.Union {
		memberConstr, err := td.getSmtConstr(smtValue, &member)
		if err != nil {
			return nil, err
		}
		orConstr = append(orConstr, memberConstr...)
	}
	return []string{fmt.Sprintf("(or %s)", strings.Join(orConstr, " "))}, nil
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
func (td *TypeTranslator) getSmtObjectConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsObject() {
		return nil, err.ErrUnsupportedType
	}

	andConstr := make([]string, 0, 64)
	// Ensure deterministic enumeration of object fields by sorting keys.
	keys := make([]string, 0, len(tp.ObjectFields))
	for k := range tp.ObjectFields {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, key := range keys {
		val := tp.ObjectFields[key]
		sel := fmt.Sprintf("(select (obj %s) \"%s\")", smtValue, key)
		if !val.IsAtomic() {
			andConstr = append(andConstr, fmt.Sprintf("(%s %s)", getTypeConstr(&val), sel))
		}

		valAnalysis, er := td.getSmtConstr(sel, &val)
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
func (td *TypeTranslator) getSmtAtomConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
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
	case types.AtomicNull:
		return []string{fmt.Sprintf("(is-ONull (atom %s))", smtValue)}, nil
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
func (td *TypeTranslator) getSmtArrConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsArray() {
		return nil, err.ErrUnsupportedType
	}
	andConstr := make([]string, 0, 64)
	andConstr = append(andConstr, fmt.Sprintf("(is-OArray %s)", smtValue))

	valAnalysis, er := td.getSmtConstr("elem", tp.ArrayType)
	if er != nil {
		return nil, er
	}
	ands := fmt.Sprintf("(and %s)", strings.Join(valAnalysis, " "))
	qvar := RandString(5)
	forall := fmt.Sprintf("(forall ((%s Int))  (let ((elem (select (arr %s) %s))) %s))", qvar, smtValue, qvar, ands)
	andConstr = append(andConstr, forall)

	return andConstr, nil
}

// getSmtRef constructs an SMT-LIB reference string by traversing a path through nested object types.
//
// Parameters:
//
//	smtvar string: The base SMT variable name.
//	path []string: The path to traverse as a slice of field names.
//	tp *types.RegoTypeDef: The starting Rego type definition.
//
// Returns:
//
//	string: The SMT-LIB reference string for the given path.
//	error: An error if the path cannot be traversed due to type mismatches.
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
