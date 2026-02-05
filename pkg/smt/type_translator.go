package smt

import (
	"fmt"
	"math/rand"
	"sort"
	"strings"
	"time"

	"github.com/open-policy-agent/opa/v1/ast"

	"github.com/vhavlena/verirego/pkg/err"
	"github.com/vhavlena/verirego/pkg/types"
)

const letterBytes = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
const letterStartBytes = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

const smtUndef = "OUndef"

// RandString returns a random SMT-LIB symbol-like string of length `n`.
//
// Behaviour:
//   - Ensures the first character is a letter so the result is a valid SMT-LIB symbol.
//   - Uses a time-based seed and draws subsequent characters from an alpha-numeric set.
//
// Parameters:
// - `n int`: Desired length.
//
// Returns:
// - `string`: Random string of length `n` (or empty if `n == 0`).
func RandString(n int) string {
	rand.Seed(time.Now().UnixNano())
	b := make([]byte, n)
	// Ensure the first character is a letter to form a valid SMT-LIB symbol
	if n > 0 {
		b[0] = letterStartBytes[rand.Intn(len(letterStartBytes))]
	}
	for i := 1; i < n; i++ {
		b[i] = letterBytes[rand.Intn(len(letterBytes))]
	}
	return string(b)
}

//----------------------------------------------------------------

// TypeTranslator handles SMT type declarations and type-related operations.
type TypeTranslator struct {
	TypeInfo *types.TypeAnalyzer // Type information for Rego terms
}

// NewTypeDefs constructs a TypeTranslator with the given type analyzer.
//
// Parameters:
// - `typeInfo *types.TypeAnalyzer`: Analyzer holding inferred types.
//
// Returns:
// - `*TypeTranslator`: New translator instance.
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

// NewBucket creates an empty Bucket with pre-allocated capacity.
//
// Returns:
// - `*Bucket`: Bucket with empty `Decls`, `Asserts`, and `TypeDecls`.
func NewBucket() *Bucket {
	return &Bucket{
		Decls:     make([]string, 0, 64),
		Asserts:   make([]string, 0, 128),
		TypeDecls: make([]string, 0, 32),
	}
}

// Append merges the contents of `other` into `b`.
//
// Parameters:
// - `other *Bucket`: Bucket to append.
func (b *Bucket) Append(other *Bucket) {
	b.Decls = append(b.Decls, other.Decls...)
	b.Asserts = append(b.Asserts, other.Asserts...)
	b.TypeDecls = append(b.TypeDecls, other.TypeDecls...)
}

//----------------------------------------------------------------

// GenerateTypeDecls generates SMT-LIB datatype/sort declarations for `usedVars`.
//
// Behaviour:
//   - Computes the maximum type depth among variables present in `usedVars`.
//   - Emits datatype declarations up to that depth.
//
// Parameters:
// - `usedVars map[string]any`: Keys are variable names to consider.
//
// Returns:
// - `*Bucket`: Bucket with `TypeDecls` populated.
// - `error`: Non-nil if generation fails.
func (td *TypeTranslator) GenerateTypeDecls(usedVars map[string]any) (*Bucket, error) {
	bucket := NewBucket()

	maxDepth := 0
	for name, tp := range td.TypeInfo.Types {
		if _, ok := usedVars[name]; !ok {
			continue
		}
		maxDepth = max(maxDepth, tp.TypeDepth())
	}

	datatypesBucket := td.getDatatypesDeclaration(maxDepth)
	bucket.Append(datatypesBucket)
	return bucket, nil
}

// GenerateVarDecl generates the SMT-LIB declaration and constraint assertion for `varName`.
//
// Parameters:
// - `varName string`: Variable name (must exist in `td.TypeInfo.Types`).
//
// Returns:
// - `*Bucket`: Bucket containing a declaration in `Decls` and constraints in `Asserts`.
// - `error`: Non-nil if generation fails.
func (td *TypeTranslator) GenerateVarDecl(varName string) (*Bucket, error) {
	bucket := NewBucket()
	tp := td.TypeInfo.Types[varName]
	varDeclBucket, er := td.getVarDeclaration(varName, &tp)
	if er != nil {
		return nil, er
	}
	bucket.Append(varDeclBucket)

	constrBucket, er := td.getSmtConstrAssert(varName, &tp)
	if er != nil {
		return nil, er
	}
	bucket.Append(constrBucket)

	return bucket, nil
}

// GenerateVarDecls generates declarations and constraints for every variable in `usedVars`.
//
// Parameters:
// - `usedVars map[string]any`: Keys are variable names to generate declarations for.
//
// Returns:
// - `*Bucket`: Aggregated bucket of `Decls` and `Asserts`.
// - `error`: Non-nil if any variable generation fails.
func (td *TypeTranslator) GenerateVarDecls(usedVars map[string]any) (*Bucket, error) {
	bucket := NewBucket()
	for name := range usedVars {
		varBucket, er := td.GenerateVarDecl(name)
		if er != nil {
			return nil, er
		}
		bucket.Append(varBucket)
	}
	return bucket, nil
}

// getTypeConstr returns the SMT predicate name enforcing a type at `depth`.
//
// Parameters:
// - `depth int`: Value depth used to choose depth-indexed predicates for arrays/objects.
// - `tp *types.RegoTypeDef`: Rego type definition.
//
// Returns:
// - `string`: SMT predicate name (e.g. `is-OString`, `is-OObj2`).
// - `error`: Non-nil for unsupported atomic kinds.
func getTypeConstr(depth int, tp *types.RegoTypeDef) (string, error) {
	if tp.IsAtomic() {
		switch tp.AtomicType {
		case types.AtomicString:
			return "is-OString", nil
		case types.AtomicInt:
			return "is-ONumber", nil
		case types.AtomicBoolean:
			return "is-OBoolean", nil
		case types.AtomicNull:
			return "is-ONull", nil
		case types.AtomicUndef:
			return "is-OUndef", nil
		case types.AtomicFunction, types.AtomicSet:
			return "", err.ErrUnsupportedAtomic
		default:
			return "", err.ErrUnsupportedAtomic
		}
	} else if tp.IsArray() {
		return fmt.Sprintf("is-OArray%d", depth), nil
	}
	return fmt.Sprintf("is-OObj%d", depth), nil
}

// getDatatypesDeclaration returns SMT-LIB datatype declarations up to `maxDepth`.
//
// Notes:
//   - `OTypeD0` represents atomic values.
//   - `OTypeD1..N` represent nested values where object/array elements refer to `OTypeD(d-1)`.
//
// Parameters:
// - `maxDepth int`: Maximum depth to declare.
//
// Returns:
// - `*Bucket`: Bucket with `TypeDecls` populated.
func (td *TypeTranslator) getDatatypesDeclaration(maxDepth int) *Bucket {
	// Simplified scheme:
	// - OTypeD0 is the atomic datatype (previously called OAtom).
	// - OTypeD1..N are depth-indexed value datatypes whose Atom constructor
	//   carries OTypeD0, and whose object/array fields also store OTypeD0,
	//   then OTypeD(d-1) for higher depths.
	bucket := NewBucket()
	bucket.TypeDecls = append(bucket.TypeDecls, `
(declare-datatypes ()
	((OTypeD0
		(OString (str String))
		(ONumber (num Int))
		(OBoolean (bool Bool))
		ONull
		OUndef
	))
)`)

	for d := 1; d <= maxDepth; d++ {
		inner := fmt.Sprintf("OTypeD%d", d-1)
		bucket.TypeDecls = append(bucket.TypeDecls, fmt.Sprintf(`
(declare-datatypes ()
  ((OTypeD%d
    (Atom%d (atom%d %s))
    (OObj%d (obj%d (Array String %s)))
    (OArray%d (arr%d (Array Int %s)))
  ))
)`, d, d, d, inner, d, d, inner, d, d, inner))
	}

	return bucket
}

// getVarDeclaration emits a `(declare-fun ...)` for `name` using `tp`'s sort.
//
// Parameters:
// - `name string`: SMT variable name.
// - `tp *types.RegoTypeDef`: Rego type definition.
//
// Returns:
// - `*Bucket`: Bucket with a single entry in `Decls`.
// - `error`: Always nil in current implementation.
func (td *TypeTranslator) getVarDeclaration(name string, tp *types.RegoTypeDef) (*Bucket, error) {
	bucket := NewBucket()
	bucket.Decls = append(bucket.Decls, fmt.Sprintf("(declare-fun %s () %s)", name, td.getSmtType(tp)))
	return bucket, nil
}

// getSmtType returns the SMT-LIB sort name for `tp`.
//
// Behaviour:
//   - Uses `tp.TypeDepth()` to select a depth-indexed sort `OTypeD<d>`.
//
// Parameters:
// - `tp *types.RegoTypeDef`: Rego type definition.
//
// Returns:
// - `string`: SMT sort name.
func (td *TypeTranslator) getSmtType(tp *types.RegoTypeDef) string {
	// With simplified scheme, atomic values are OTypeD0 and non-atomic values
	// start at OTypeD1.
	dpth := max(tp.TypeDepth(), 0)
	return fmt.Sprintf("OTypeD%d", dpth)
}

// getSmtConstrAssert wraps the constraints for `smtValue` in a single SMT `(assert ...)`.
//
// Parameters:
// - `smtValue string`: SMT expression/value to constrain.
// - `tp *types.RegoTypeDef`: Expected Rego type.
//
// Returns:
// - `*Bucket`: Bucket with one `(assert ...)` in `Asserts`.
// - `error`: Non-nil if constraint generation fails.
func (td *TypeTranslator) getSmtConstrAssert(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	bucket := NewBucket()
	andBucket, er := td.getSmtConstr(smtValue, tp)
	if er != nil {
		return nil, err.ErrSmtConstraints(er)
	}
	assert := strings.Join(andBucket.Asserts, " ")
	bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(assert (and %s))", assert))
	return bucket, nil
}

// getSmtConstr generates SMT constraint fragments for `smtValue` of type `tp`.
//
// Parameters:
// - `smtValue string`: SMT expression/value to constrain.
// - `tp *types.RegoTypeDef`: Expected Rego type.
//
// Returns:
// - `*Bucket`: Bucket with constraint fragments in `Asserts`.
// - `error`: Non-nil if the type is unsupported or constraint generation fails.

func (td *TypeTranslator) getSmtConstr(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
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

// getSmtUnionConstr generates constraints for a union type.
//
// Behaviour:
//   - Produces a single SMT `(or ...)` over member-constraint conjunctions.
//
// Parameters:
// - `smtValue string`: SMT expression/value to constrain.
// - `tp *types.RegoTypeDef`: Union type definition.
//
// Returns:
// - `*Bucket`: Bucket with one `(or ...)` in `Asserts`.
// - `error`: Non-nil if `tp` is not a union or member constraints fail.

func (td *TypeTranslator) getSmtUnionConstr(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	if !tp.IsUnion() {
		return nil, err.ErrUnsupportedType
	}

	bucket := NewBucket()

	orConstr := make([]string, 0, 64)
	for _, member := range tp.Union {
		memberBucket, err := td.getSmtConstr(smtValue, &member)
		if err != nil {
			return nil, err
		}
		orConstr = append(orConstr, memberBucket.Asserts...)
	}
	bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(or %s)", strings.Join(orConstr, " ")))
	return bucket, nil
}

// getSmtObjectConstr generates SMT-LIB constraints for an object value.
//
// Behaviour:
//   - Assert the object predicate at depth: `(is-OObj<d> <smtValue>)`.
//   - For each declared field (sorted): select `(select (obj<d> <smtValue>) "<field>")`,
//     recurse into the field type and add a type predicate for non-atomic fields.
//   - If additional properties are disallowed or an additional-property type is set,
//     emit a `(forall ((k String)) ...)` that requires keys to be explicit or
//     have `OUndef` / satisfy the additional type.
//
// Parameters:
// - `smtValue string`: SMT expression for the object value.
// - `tp *types.RegoTypeDef`: Rego object type (must satisfy `IsObject()`).
//
// Returns:
// - `[]string`: Constraint fragments (combine with `(and ...)` for assertions).
// - `error`: Non-nil if `tp` is not an object or a field type is missing.
func (td *TypeTranslator) getSmtObjectConstr(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	if !tp.IsObject() {
		return nil, err.ErrUnsupportedType
	}

	bucket := NewBucket()

	depth := max(tp.TypeDepth(), 0)
	bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(is-OObj%d %s)", depth, smtValue))
	// Ensure deterministic enumeration of object fields by sorting keys.
	keys := tp.ObjectFields.GetKeys()
	sort.Strings(keys)

	for _, key := range keys {
		val, found := tp.ObjectFields.Get(key)
		if !found {
			return nil, err.ErrSmtFieldConstraints(key, err.ErrTypeNotFound)
		}
		sel := fmt.Sprintf("(select (obj%d %s) \"%s\")", depth, smtValue, key)
		if !val.IsAtomic() {
			constr, err := getTypeConstr(depth-1, val)
			if err != nil {
				return nil, err
			}
			bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(%s %s)", constr, sel))
		}

		valAnalysis, er := td.getSmtConstr(sel, val)
		if er != nil {
			return nil, err.ErrSmtFieldConstraints(key, er)
		}
		bucket.Asserts = append(bucket.Asserts, valAnalysis.Asserts...)
	}

	// Helper to build a universal quantification over all string keys
	// If additional are not allowed: forall k:String. (k in explicitKeys) or value_at_k is undefined
	// If additional allowed and AdditionalPropKey exists: forall k:String. (k in explicitKeys) or value_at_k matches additional type constructor
	if !tp.ObjectFields.AllowAdditional || tp.ObjectFields.HasSetAdditionalProperties() {
		kVar := RandString(5)
		disj := make([]string, 0, len(keys)+1)
		for _, k := range keys {
			disj = append(disj, fmt.Sprintf("(= %s \"%s\")", kVar, k))
		}

		defSelect := fmt.Sprintf("(select (obj%d %s) %s)", depth, smtValue, kVar)
		var defVal string
		if !tp.ObjectFields.AllowAdditional {
			// Default values at the element depth.
			defVal = fmt.Sprintf("(is-OUndef %s)", defSelect)
		} else {
			apType := tp.ObjectFields.Fields[types.AdditionalPropKey]
			pred, err := getTypeConstr(depth-1, &apType)
			if err != nil {
				return nil, err
			}
			defVal = fmt.Sprintf("(%s %s)", pred, defSelect)
			defVal = defVal + " (is-OUndef " + defSelect + ")"
		}

		disj = append(disj, defVal)
		body := fmt.Sprintf("(or %s)", strings.Join(disj, " "))
		bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(forall ((%s String)) %s)", kVar, body))
	}
	return bucket, nil
}

//----------------------------------------------------------------
// Object store-based construction (simple objects)

// getSmtUndefValue returns an `OUndef` value at a given value-depth.
//
// Behaviour:
//   - For depth 0: returns `OUndef`.
//   - For depth > 0: returns nested `Atom<d>` constructors around `OUndef`.
//
// Parameters:
// - `depth int`: Value depth.
//
// Returns:
// - `string`: SMT expression of the appropriate `OTypeD<depth>` sort.
func (td *TypeTranslator) getSmtUndefValue(depth int) string {
	if depth <= 0 {
		return smtUndef
	}
	val := smtUndef
	for d := 1; d <= depth; d++ {
		val = fmt.Sprintf("(Atom%d %s)", d, val)
	}
	return val
}

// getSmtLeafVarDefs emits declaration/assertions for an atomic leaf symbol.
//
// Notes:
//   - Declares `leafName` as a 0-arity SMT function returning the atomic sort.
//   - Adds an assertion restricting the value to the expected atomic constructor.
//
// Parameters:
// - `leafName string`: SMT symbol to declare.
// - `leafType *types.RegoTypeDef`: Leaf type (must be atomic).
//
// Returns:
// - `*Bucket`: Bucket with the declaration in `Decls` and assertions in `Asserts`.
// - `error`: Non-nil if `leafType` is nil or non-atomic.
func (td *TypeTranslator) getSmtLeafVarDefs(leafName string, leafType *types.RegoTypeDef) (*Bucket, error) {
	if leafType == nil || !leafType.IsAtomic() {
		return nil, err.ErrUnsupportedType
	}

	bucket := NewBucket()
	leafSort := td.getSmtType(leafType)

	bucket.Decls = append(bucket.Decls, fmt.Sprintf("(declare-fun %s () %s)", leafName, leafSort))

	// Constrain the backing constant to be of the desired atomic constructor.
	constrBucket, err2 := td.getSmtAtomConstr(leafName, leafType)
	if err2 != nil {
		return nil, err2
	}
	for _, c := range constrBucket.Asserts {
		bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(assert %s)", c))
	}

	return bucket, nil
}

// getSmtObjStoreExpr builds an SMT expression for a *simple* object using array `store`.
//
// Notes:
//   - "Simple object" means depth-1 object with only atomic leaf fields.
//   - This intentionally ignores `AllowAdditional` / additionalProperties.
//
// Parameters:
// - `tp *types.RegoTypeDef`: Object type (must be a simple object).
//
// Returns:
// - `string`: SMT expression of sort `OTypeD<depth>` representing the object.
// - `*Bucket`: Bucket containing leaf declarations and leaf constraints.
// - `error`: Non-nil if `tp` is not a supported simple object.
func (td *TypeTranslator) getSmtObjStoreExpr(tp *types.RegoTypeDef) (string, *Bucket, error) {
	if tp == nil || !tp.IsObject() {
		return "", nil, err.ErrUnsupportedType
	}

	depth := max(tp.TypeDepth(), 0)
	if depth != 1 {
		// "simple object" = object with only atomic leaf fields (no nested objects/arrays/unions)
		return "", nil, err.ErrUnsupportedType
	}

	keys := tp.ObjectFields.GetKeys()
	sort.Strings(keys)

	usedVars := make(map[string]string)
	bucket := NewBucket()

	innerDepth := depth - 1
	innerSort := fmt.Sprintf("OTypeD%d", innerDepth)
	defaultVal := td.getSmtUndefValue(innerDepth)
	arrExpr := fmt.Sprintf("((as const (Array String %s)) %s)", innerSort, defaultVal)

	for _, key := range keys {
		fieldType, found := tp.ObjectFields.Get(key)
		if !found {
			return "", nil, err.ErrTypeNotFound
		}
		if fieldType == nil || !fieldType.IsAtomic() {
			return "", nil, err.ErrUnsupportedType
		}

		leafName := td.getFreshVariable("leaf_"+key, usedVars)
		usedVars[leafName] = leafName

		leafBucket, leafErr := td.getSmtLeafVarDefs(leafName, fieldType)
		if leafErr != nil {
			return "", nil, leafErr
		}
		bucket.Append(leafBucket)

		arrExpr = fmt.Sprintf("(store %s \"%s\" %s)", arrExpr, key, leafName)
	}

	objExpr := fmt.Sprintf("(OObj%d %s)", depth, arrExpr)
	return objExpr, bucket, nil
}

// GetSmtObjStoreExpr is an exported wrapper around `getSmtObjStoreExpr`.
//
// Parameters:
// - `tp *types.RegoTypeDef`: Object type.
//
// Returns:
// - `string`: SMT expression for the object.
// - `*Bucket`: Bucket with leaf declarations/assertions.
// - `error`: Non-nil if the object type is unsupported.
func (td *TypeTranslator) GetSmtObjStoreExpr(tp *types.RegoTypeDef) (string, *Bucket, error) {
	return td.getSmtObjStoreExpr(tp)
}

// getSmtObjectConstrStore constructs a simple object via `store` and asserts equality.
//
// Parameters:
// - `smtValue string`: SMT symbol/expression to equate to the constructed object.
// - `tp *types.RegoTypeDef`: Object type (must be a supported simple object).
//
// Returns:
// - `*Bucket`: Bucket containing leaf declarations/assertions plus the equality assertion.
// - `error`: Non-nil if object construction fails.
func (td *TypeTranslator) getSmtObjectConstrStore(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	objExpr, defsBucket, err2 := td.getSmtObjStoreExpr(tp)
	if err2 != nil {
		return nil, err2
	}

	bucket := NewBucket()
	bucket.Append(defsBucket)
	bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(assert (= %s %s))", smtValue, objExpr))
	return bucket, nil
}

// GetSmtObjectConstrStore is an exported wrapper around `getSmtObjectConstrStore`.
//
// Parameters:
// - `smtValue string`: SMT symbol/expression to equate to a constructed object.
// - `tp *types.RegoTypeDef`: Object type.
//
// Returns:
// - `*Bucket`: Bucket containing required declarations/assertions.
// - `error`: Non-nil if object construction fails.
func (td *TypeTranslator) GetSmtObjectConstrStore(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	return td.getSmtObjectConstrStore(smtValue, tp)
}

// getSmtAtomConstr generates a single type predicate constraint for an atomic value.
//
// Parameters:
// - `smtValue string`: SMT expression/value to constrain.
// - `tp *types.RegoTypeDef`: Atomic type.
//
// Returns:
// - `*Bucket`: Bucket containing one constraint fragment in `Asserts`.
// - `error`: Non-nil if `tp` is not atomic or unsupported.
func (td *TypeTranslator) getSmtAtomConstr(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	if !tp.IsAtomic() {
		return nil, err.ErrUnsupportedType
	}
	constr, err := getTypeConstr(0, tp)
	if err != nil {
		return nil, err
	}
	bucket := NewBucket()
	bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(%s %s)", constr, smtValue))
	return bucket, nil
}

// getSmtArrConstr generates constraints for an array value and its element type.
//
// Behaviour:
//   - Asserts `(is-OArray<d> smtValue)`.
//   - Adds a `forall` over indices constraining each selected element.
//
// Parameters:
// - `smtValue string`: SMT expression/value to constrain.
// - `tp *types.RegoTypeDef`: Array type.
//
// Returns:
// - `*Bucket`: Bucket containing array and element constraints.
// - `error`: Non-nil if `tp` is not an array or element constraints fail.
func (td *TypeTranslator) getSmtArrConstr(smtValue string, tp *types.RegoTypeDef) (*Bucket, error) {
	if !tp.IsArray() {
		return nil, err.ErrUnsupportedType
	}

	bucket := NewBucket()
	depth := max(tp.TypeDepth(), 0)
	bucket.Asserts = append(bucket.Asserts, fmt.Sprintf("(is-OArray%d %s)", depth, smtValue))

	valAnalysis, er := td.getSmtConstr("elem", tp.ArrayType)
	if er != nil {
		return nil, er
	}
	ands := fmt.Sprintf("(and %s)", strings.Join(valAnalysis.Asserts, " "))
	qvar := RandString(5)
	forall := fmt.Sprintf("(forall ((%s Int))  (let ((elem (select (arr%d %s) %s))) %s))", qvar, depth, smtValue, qvar, ands)
	bucket.Asserts = append(bucket.Asserts, forall)

	return bucket, nil
}

// getSmtRef constructs an SMT select-chain by traversing an object-typed path.
//
// Parameters:
// - `smtvar string`: Base SMT variable/expression.
// - `path []string`: Field-name path to traverse.
// - `tp *types.RegoTypeDef`: Starting type for traversal.
//
// Returns:
// - `string`: SMT expression selecting the nested value.
// - `*types.RegoTypeDef`: Type definition of the selected value.
// - `error`: Non-nil if a non-object is traversed or a field is missing.
func getSmtRef(smtvar string, path []string, tp *types.RegoTypeDef) (string, *types.RegoTypeDef, error) {
	smtref := smtvar
	actType := tp
	for _, p := range path {
		if !actType.IsObject() {
			return "", nil, fmt.Errorf("only object types can be used in references")
		}
		val, found := actType.ObjectFields.Get(p)
		if !found {
			return "", nil, fmt.Errorf("field not found in object type: %s", p)
		}
		depth := max(actType.TypeDepth()-1, 0)
		actType = val
		smtref = fmt.Sprintf("(select (obj%d %s) \"%s\")", depth, smtref, p)
	}
	return smtref, actType, nil
}

// refToPath converts a Rego AST ref into a string path.
//
// Parameters:
// - `ref ast.Ref`: Rego reference.
//
// Returns:
// - `[]string`: Path segments.
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

// removeQuotes strips a single leading/trailing double quote pair, if present.
//
// Parameters:
// - `s string`: Input string.
//
// Returns:
// - `string`: Unquoted string if quoted; otherwise `s` unchanged.
func removeQuotes(s string) string {
	if len(s) < 2 {
		return s
	}
	if s[0] == '"' && s[len(s)-1] == '"' {
		return s[1 : len(s)-1]
	}
	return s
}

// getSchemaVar constructs a schema variable name for `input.review.object.<name>`.
//
// Parameters:
// - `ref ast.Ref`: Reference expected to have 4 terms.
//
// Returns:
// - `string`: Dot-separated schema variable name.
func getSchemaVar(ref ast.Ref) string {
	// input.review.object.<name>
	return fmt.Sprintf("%s.%s.%s.%s", removeQuotes(ref[0].String()), removeQuotes(ref[1].String()), removeQuotes(ref[2].String()), removeQuotes(ref[3].String()))
}

// getParamVar constructs a parameter variable name for `input.parameters.<name>`.
//
// Parameters:
// - `ref ast.Ref`: Reference expected to have 3 terms.
//
// Returns:
// - `string`: Dot-separated parameter variable name.
func getParamVar(ref ast.Ref) string {
	// input.parameters.<name>
	return fmt.Sprintf("%s.%s.%s", removeQuotes(ref[0].String()), removeQuotes(ref[1].String()), removeQuotes(ref[2].String()))
}

// getFreshVariable returns a fresh SMT symbol name that does not clash with known names.
//
// Behaviour:
//   - Avoids names in `td.TypeInfo.Types` and the values of `usedVars`.
//   - If `prefix` is taken, appends `_<n>` until a free name is found.
//
// Parameters:
// - `prefix string`: Prefix for the generated name.
// - `usedVars map[string]string`: Additional names to avoid (values are treated as used).
//
// Returns:
// - `string`: Fresh variable name.
func (td *TypeTranslator) getFreshVariable(prefix string, usedVars map[string]string) string {
	// Collect all used names: keys in TypeDefs.TypeInfo.Types and values in VarMap
	used := make(map[string]struct{})
	if td.TypeInfo != nil {
		for name := range td.TypeInfo.Types {
			used[name] = struct{}{}
		}
	}
	for _, v := range usedVars {
		used[v] = struct{}{}
	}
	// Try to find a fresh variable name
	for i := 0; ; i++ {
		varName := prefix
		if i > 0 {
			varName = prefix + fmt.Sprintf("_%d", i)
		}
		if _, exists := used[varName]; !exists {
			return varName
		}
	}
}

// getAtomValue returns the SMT atomic accessor for `name` according to `tp`.
//
// Notes:
//   - For depth 0 values, wraps directly with `str`/`num`/`bool`.
//   - For depth > 0, unwraps via `atom<d>` before applying `str`/`num`/`bool`.
//
// Parameters:
// - `name string`: SMT expression to wrap (e.g. a variable name or select-chain).
// - `tp *types.RegoTypeDef`: Atomic type definition.
//
// Returns:
// - `string`: SMT expression accessing the underlying primitive.
// - `error`: Non-nil for unsupported atomic kinds.
func (td *TypeTranslator) getAtomValue(name string, tp *types.RegoTypeDef) (string, error) {
	depth := max(tp.TypeDepth(), 0)
	switch tp.AtomicType {
	case types.AtomicString:
		if depth == 0 {
			return fmt.Sprintf("(str %s)", name), nil
		}
		return fmt.Sprintf("(str (atom%d %s))", depth, name), nil
	case types.AtomicInt:
		if depth == 0 {
			return fmt.Sprintf("(num %s)", name), nil
		}
		return fmt.Sprintf("(num (atom%d %s))", depth, name), nil
	case types.AtomicBoolean:
		if depth == 0 {
			return fmt.Sprintf("(bool %s)", name), nil
		}
		return fmt.Sprintf("(bool (atom%d %s))", depth, name), nil
	case types.AtomicNull:
		return "ONull", nil
	case types.AtomicUndef:
		return "OUndef", nil
	case types.AtomicFunction, types.AtomicSet:
		return "", err.ErrUnsupportedAtomic
	default:
		return "", err.ErrUnsupportedAtomic
	}
}

// getSmtValue returns an SMT expression for `smt` consistent with `tp`.
//
// Behaviour:
//   - For atomic types, returns a primitive accessor expression (via `getAtomValue`).
//   - For objects/arrays/unions, returns `smt` unchanged.
//
// Parameters:
// - `smt string`: Base SMT expression or symbol.
// - `tp *types.RegoTypeDef`: Expected type.
//
// Returns:
// - `string`: SMT expression suitable for use in generated assertions.
// - `error`: Non-nil if an atomic conversion is unsupported.
func (td *TypeTranslator) getSmtValue(smt string, tp *types.RegoTypeDef) (string, error) {
	// If the type is atomic, convert to the wrapped atom form (num/str/bool etc.).
	// For non-atomic types (object, array, union) return the SMT expression
	// as-is (e.g. select chains or variable names) so callers can use it
	// directly in generated SMT assertions.
	if tp.IsAtomic() {
		return td.getAtomValue(smt, tp)
	}
	// For objects/arrays/unions we don't wrap into atom constructors here;
	// the SMT expression (smt) already represents the proper select/var form.
	return smt, nil
}

// getVarValue returns an SMT expression for the variable `name` according to inferred type.
//
// Parameters:
// - `name string`: Variable name.
//
// Returns:
// - `string`: SMT expression for the variable (atomic accessors or raw symbol).
// - `error`: Non-nil if the variable type is missing or atomic conversion fails.
func (td *TypeTranslator) getVarValue(name string) (string, error) {
	tp, ok := td.TypeInfo.Types[name]
	if !ok {
		return "", err.ErrTypeNotFound
	}
	return td.getSmtValue(name, &tp)
}
