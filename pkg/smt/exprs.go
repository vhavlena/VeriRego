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
	TypeTrans   *TypeTranslator // Type definitions and type-related operations
	funcMap     map[string]Function
	context     *TransContext // Context to collect generated SMT declarations, assertions, and variable mappings
	packagePath *ast.Ref      // Path of the currently processed package (TODO: this needs to be changed when introducing import of other Rego modules)
}

// NewExprTranslator creates a new ExprTranslator instance.
func NewExprTranslator(typeTrans *TypeTranslator) *ExprTranslator {
	return &ExprTranslator{
		TypeTrans:   typeTrans,
		funcMap:     GetBuiltinFuncMap(),
		context:     NewTransContext(),
		packagePath: typeTrans.TypeInfo.GetPackagePath(),
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

// varDef represents definition of a local variable
type varDef struct {
	name  string
	value SmtValue
}

func (et *ExprTranslator) gatherQuantFromExpr(expr *ast.Expr, out map[string]bool) {
	if term, ok := expr.Terms.(*ast.Term); ok {
		et.gatherQuantFromTerm(term, out)
		return
	}

	terms, ok := expr.Terms.([]*ast.Term)
	if !ok { return }

	et.gatherQuantFromTerms(terms[1:], out)
}

func (et *ExprTranslator) gatherQuantFromTerms(terms []*ast.Term, out map[string]bool) {
	for _, term := range terms {
		et.gatherQuantFromTerm(term, out)
	}
}

func (et *ExprTranslator) gatherQuantFromTerm(term *ast.Term, out map[string]bool) {
		switch v := term.Value.(type) {
		case ast.Var:
			name := removeQuotes(v.String())
			if et.TypeTrans.TypeInfo.VarClassification.Quantified[name] {
				out[name] = true
			}
		case ast.Ref:
			et.gatherQuantFromTerms(v[1:], out)
		case ast.Call:
			et.gatherQuantFromTerms(v[1:], out)
		}
}

// GatherQuant returns a set of all quantifiers present in giver body
func (et *ExprTranslator) GatherQuant(ruleBody *ast.Body) map[string]bool {
	out := make(map[string]bool)
	for _, expr := range *ruleBody {
		et.gatherQuantFromExpr(expr, out)
	}
	return out
}

// BodyToSmt parses a rule body for transformation into SMT
//
// Returns:
//
//	*SmtProposition: Proposition encoding the constraints present in the body
//	[]varDef: List of definitions for local variables
//	error
func (et *ExprTranslator) BodyToSmt(ruleBody *ast.Body) (*SmtProposition, []varDef, error) {
	bodySmts := make([]SmtProposition, 0, len(*ruleBody))
	definedVars := make(map[string]bool, 0)
	localVarDefs := make([]varDef, 0)
	for _, expr := range *ruleBody {
		// single term
		if term, ok := expr.Terms.(*ast.Term); ok {
			smtVal, err := et.termToSmtValue(term)
			if err != nil {
				return nil, localVarDefs, err
			}
			bodySmts = append(bodySmts, *smtVal.Holds())
			continue
		}

		// call
		terms, ok := expr.Terms.([]*ast.Term)
		if !ok || len(terms) == 0 {
			return nil, localVarDefs, verr.ErrUnexpected
		}

		op, err := et.termToOperation(terms[0])
		if err != nil {
			return nil, localVarDefs, err
		}

		arity := len(op.args)
		params := make([]*SmtValue, len(terms)-1)
		for i := 1; i < len(terms); i++ {
			val, err := et.termToSmtValue(terms[i])
			if err != nil {
				return nil, localVarDefs, err
			}
			params[i-1] = val
		}

		if arity+1 == len(params) { // the return is a part of the call
			val, err := op.SmtCall(params[:len(params)-1])
			if err != nil {
				return nil, localVarDefs, err
			}
			def := varDef{params[len(params)-1].String(), *val.WrapToDepth(op.result.depth)}
			localVarDefs = append(localVarDefs, def)
			definedVars[def.name] = true
			continue
		}

		// we handle ast.Equality separately, because it can be both assignment and comparison, based on the context
		if op.name == ast.Equality.Name {
			if variable, ok := terms[1].Value.(ast.Var); ok {
				name := removeQuotes(variable.String())
				if definedVars[name] != true {
					rhs := params[1]
					// Wrap the RHS constant to the declared type depth of the target variable so
					// the let-binding has the correct sort (e.g. (ONumber 1) instead of 1).
					if tp, ok := et.TypeTrans.TypeInfo.Types[name]; ok {
						if wrapped := rhs.WrapToDepth(tp.TypeDepth()); wrapped != nil {
							rhs = wrapped
						}
					}
					localVarDefs = append(localVarDefs, varDef{name, *rhs})
					definedVars[name] = true
				} else {
					varSmt, err := NewSmtValueFromVar(variable, et)
					if err != nil {
						return nil, nil, err
					}
					bodySmts = append(bodySmts, *varSmt.Equals(params[1]))
				}
				continue
			}
		}

		// normal function call
		bodySmt, err := op.SmtCall(params)
		if err != nil {
			return nil, localVarDefs, err
		}
		bodySmts = append(bodySmts, *bodySmt.Holds())
	}

	bodySmt := And(bodySmts)
	return bodySmt, localVarDefs, nil
}

// termToOperation tries to get a Function represented by the input opTerm.
func (et *ExprTranslator) termToOperation(opTerm *ast.Term) (*Function, error) {
	opStr := removeQuotes(opTerm.String())
	op, ok := et.funcMap[opStr]
	if !ok {
		opParts := strings.Split(opStr, ".") // TODO: handle references properly (data.<module>.funcName)
		opStr = opParts[len(opParts)-1]
		op, ok = et.funcMap[opStr]
		if !ok {
			return nil, verr.ErrFunctionNotFound(opStr)
		}
	}
	return &op, nil
}

// termToSmtValue transforms given term into SmtValue
func (et *ExprTranslator) termToSmtValue(term *ast.Term) (*SmtValue, error) {
	switch v := term.Value.(type) {
	case ast.String:
		return NewSmtValueFromString(string(v)), nil
	case ast.Number:
		if val, ok := v.Int(); ok {
			return NewSmtValueFromInt(val), nil
		}
		return nil, verr.ErrInvalidInt(v.String())
	case ast.Boolean:
		return NewSmtValueFromBoolean(bool(v)), nil
	case *ast.Array:
		return et.arrayToSmt(v)
	case ast.Object:
		return et.objectToSmt(v)
	case ast.Set:
		return nil, verr.ErrNotImplemented("sets")
	case ast.Var:
		return NewSmtValueFromVar(v, et)
	case ast.Ref:
		return et.refToSmtValue(v)
	case ast.Call:
		// Handle string functions and other builtins
		op, err := et.termToOperation(v[0])
		if err != nil {
			return nil, err
		}
		params := make([]*SmtValue, len(v)-1)
		for i := 1; i < len(v); i++ {
			sv, err := et.termToSmtValue(v[i])
			if err != nil {
				return nil, err
			}
			params[i-1] = sv
		}
		return op.SmtCall(params)
	default:
		return nil, fmt.Errorf("%w: %T", verr.ErrUnsupportedTermType, v)
	}
}

// arrayToSmt converts a Rego array to an SmtValue representing the corresponding SMT-LIB expression.
// it works for arrays with explicit elements (e.g. arr := [1,2,3])
// now experimenting with the sequence based approach 
//
// Parameters:
//
//	arr *ast.Array: The Rego array to convert.
//
// Returns:
//
//	*SmtValue: An SmtValue representing the SMT-LIB expression for the array.
//	error: An error if type information is missing or conversion fails.
func (et *ExprTranslator) arrayToSmt(arr *ast.Array) (*SmtValue, error) {
	tp, ok := et.TypeTrans.TypeInfo.Types[arr.String()]
	if !ok {
		return nil, verr.ErrTypeNotFound(arr.String())
	}

	// We cannot use seq.nth and the concatenation seq.++ for empty arrays
	// If the sequence is empty, we just return a constant empty array
	if arr.Len() == 0 {
		depth := tp.TypeDepth()
        return &SmtValue {
			// TODO: can we return depth-1 here?
			value: fmt.Sprintf("(OArray%d (as seq.empty (Seq OTypeD%d)))", depth, depth-1),
			depth: depth,
		}, nil
	}

	depth := tp.TypeDepth()
	// arrSmt := createConstArray("Int", depth)
	elements := make([]string, arr.Len())
	// We wrap each element and add it as an element of the sequence
	// using seq.unit
	for index := range arr.Len() {
		val := arr.Elem(index)
		valSmt, err := et.termToSmtValue(val)
		if err != nil {
			return nil, err
		}
		valSmt = valSmt.WrapToDepth(depth - 1)
		// arrSmt = fmt.Sprintf("(store %s %d %s)", arrSmt, index, valSmt.String())
		elements[index] = fmt.Sprintf("(seq.unit %s)", valSmt.String())
	}

	// seq.++ requires 2+ arguments, so we handle the single element case separately
	if len(elements) == 1 {
		return &SmtValue{
			value: fmt.Sprintf("(OArray%d %s)", depth, elements[0]),
			depth: depth,
		}, nil
	}

	joinedArr := strings.Join(elements, " ")

	// joined elements are wrapped in the OArray constructor of the appropriate depth
	return &SmtValue{
		value: fmt.Sprintf("(OArray%d (seq.++ %s))", depth, joinedArr),
		depth: depth,
	}, nil
}

// objectToSmt transforms a constant Rego object into SMT representation.
func (et *ExprTranslator) objectToSmt(obj ast.Object) (*SmtValue, error) {
	tp, ok := et.TypeTrans.TypeInfo.Types[obj.String()]
	if !ok {
		return nil, verr.ErrTypeNotFound(obj.String())
	}

	depth := tp.TypeDepth()
	objSmt := createConstArray("String", depth)

	for _, key := range obj.Keys() {
		val := obj.Get(key)
		valSmt, err := et.termToSmtValue(val)
		if err != nil {
			return nil, err
		}
		valSmt = valSmt.WrapToDepth(depth - 1)
		objSmt = fmt.Sprintf("(store %s %s %s)", objSmt, key.String(), valSmt.String())
	}

	return &SmtValue{
		value: fmt.Sprintf("(OObj%d %s)", depth, objSmt),
		depth: depth,
	}, nil
}

// createConstArray is a helper function for creating an empty SMT array for values of specified depth.
// keyType "Int" is used for arrays
// keyType "String" is used for objects
func createConstArray(keyType string, depth int) string {
	constElem := NewSmtValue("OUndef", 0).WrapToDepth(depth-1)
	return fmt.Sprintf("((as const (Array %s OTypeD%d)) %s)", keyType, depth-1, constElem)
}

// refToSmtValue converts a Rego reference (ast.Ref) to an SmtValue.
// It resolves the base variable name depending on the reference prefix
// (input.*, data.*, or fallback to the last path component), looks up the
// type, navigates the field path via getSmtRef, and wraps the result.
func (et *ExprTranslator) refToSmtValue(ref ast.Ref) (*SmtValue, error) {
	if len(ref) == 0 {
		return nil, verr.ErrUnexpected
	}

	head := ref[0].Value.String()
	var name string
	rest := ref[1:]
	prefix := *et.packagePath
	if ref.HasPrefix(prefix) && len(prefix) != 0 {
		// Rule variable: <module-prefix>.<variable> ... e.g. data.test.foo
		name = removeQuotes(ref[len(prefix)].String())
		rest = ref[len(prefix)+1:]
	} else if len(ref) >= 2 && head == "input" {
		name = "input"
	} else if len(ref) >= 2 && head == "data" && et.TypeTrans.TypeInfo.DataSchema != nil {
		dataPath := refToPath(ref[1:])
		// Only treat as a data schema reference if the path actually resolves through
		// Types["data"]. Rule variables appear as data.<module>.<variable> and are
		// not registered under the "data" object type.
		if dataTp, ok := et.TypeTrans.TypeInfo.Types["data"]; ok {
			if _, exists := dataTp.GetTypeFromPath(types.FromGroundPath(dataPath)); exists {
				name = "data"
			} else {
				return nil, verr.ErrTypeNotFound(ref.String())
			}
		}
	} else {
		name = ref[0].String()
	}

	// TODO: direct arr comparison val := [1,2,3] input.user.numero[0] == val[0] fails
	// on val[0] here;; val is considered without name, but head is "__lv0" (the generated identifier)
	tp, ok := et.TypeTrans.TypeInfo.Types[name]
	if !ok {
		return nil, verr.ErrTypeNotFound(name)
	}
	smtRef, actType, err := et.GetSmtRef(name, &tp, &rest)
	if err != nil {
		return nil, err
	}
	// Return the raw OType expression without applying the atom extractor.
	// Extraction (num/str/bool) is deferred to the point of use (e.g. refToSmt
	// for operation arguments, or getVarValue for let-bound variable lookups).
	return &SmtValue{
		value:   smtRef.value,
		depth:   smtRef.depth,
		atomics: getAtomicTypes(*actType),
	}, nil
}

func (et *ExprTranslator) GetSmtRef(base string, tp *types.RegoTypeDef, rest *ast.Ref) (*SmtValue, *types.RegoTypeDef, error) {
	smtref := NewSmtValue(base, tp.TypeDepth())
	actType := tp
	for _, term := range *rest {
		switch actType.Kind {
		case types.KindObject:
			_, err := et.GetObjSelect(smtref, actType, term) // TODO: treat expects
			if err != nil {
				return nil, nil, err
			}
		case types.KindArray:
			_, err := et.GetArrSelect(smtref, actType, term) // TODO: treat expects
			if err != nil {
				return nil, nil, err
			}
		case types.KindUnion:
			panic("TODO")
		default:
			return nil, nil, fmt.Errorf("only object types can be used in references")
		}
	}
	return smtref, actType, nil
	// TODO: also support sets
	// TODO: also support unions
}

type expect struct {
	value string
	tp    *types.RegoTypeDef
}

func (et *ExprTranslator) GetObjSelect(val *SmtValue, actType *types.RegoTypeDef, term *ast.Term) (*expect, error) {
	if len(actType.ObjectFields.Fields) == 0 {
		// FIXME: this is not actually an error, but it should evaulate to undef
		return nil, verr.ErrAccessingEmptyObject(val.String())
	}

	var exp expect
	strType := types.NewAtomicType(types.AtomicString)
	switch v := term.Value.(type) {
	case ast.String:
		key := removeQuotes(v.String())
		tp, found := actType.ObjectFields.Get(key)
		if !found {
			return nil, verr.ErrMissingObjectKey(val.String(), key)
		}
		*val = *val.SelectObj(`"`+key+`"`)
		*val = *val.UnwrapToDepth(tp.TypeDepth())
		*actType = *tp;
	case ast.Var:
		name := removeQuotes(v.String())
		varTp := et.TypeTrans.TypeInfo.Types[name]
		if varTp.IsAtomic() {
			if varTp.AtomicType != types.AtomicString {
				return nil, verr.ErrUnexpectedValueType(name, "string")
			}
			tp := actType.ObjectFields.UnionizeFields()
			key := fmt.Sprintf("(str %s)", name)
			*val = *val.SelectObj(key)
			*val = *val.UnwrapToDepth(tp.TypeDepth())
			*actType = tp;
			exp = expect{ key, &strType }
		} else {
			// TODO: it can be union
			return nil, verr.ErrUnexpectedValueType(name, "string")
		}
	case ast.Ref:
		keyVal, err := et.refToSmtValue(v)
		if err != nil {
			return nil, err
		}
		key, err := keyVal.AsString()
		if err != nil {
			return nil, err
		}
		tp := actType.ObjectFields.UnionizeFields()
		*val = *val.SelectObj(key.String())
		*val = *val.UnwrapToDepth(tp.TypeDepth())
		*actType = tp;
		exp = expect{ key.String(), &strType }
	default:
		panic("todo: implement")
	}

	return &exp, nil
}

// TODO: only homogenous arrays
// TODO: treat index overflow
func (et *ExprTranslator) GetArrSelect(val *SmtValue, actType *types.RegoTypeDef, term *ast.Term) (*expect, error) {
	var exp expect
	intType := types.NewAtomicType(types.AtomicInt)
	switch v := term.Value.(type) {
	case ast.Number:
		key := v.String()
		tp := actType.ArrayType
		*val = *val.SelectArr(key)
		*val = *val.UnwrapToDepth(tp.TypeDepth())
		*actType = *tp;
	case ast.Var:
		name := removeQuotes(v.String())
		varTp := et.TypeTrans.TypeInfo.Types[name]
		if varTp.IsAtomic() {
			if varTp.AtomicType != types.AtomicInt {
				return nil, verr.ErrUnexpectedValueType(name, "int")
			}
			tp := actType.ArrayType // TODO: change for heterogenous arrays
			key := fmt.Sprintf("(num %s)", name)
			*val = *val.SelectArr(key)
			*val = *val.UnwrapToDepth(tp.TypeDepth())
			*actType = *tp;
			exp = expect{ key, &intType }
		} else {
			// TODO: it can be union
			return nil, verr.ErrUnexpectedValueType(name, "string")
		}
	case ast.Ref:
		keyVal, err := et.refToSmtValue(v)
		if err != nil {
			return nil, err
		}
		key, err := keyVal.AsInt()
		if err != nil {
			return nil, err
		}
		tp := actType.ArrayType
		*val = *val.SelectArr(key.String())
		*val = *val.UnwrapToDepth(tp.TypeDepth())
		*actType = *tp;
		exp = expect{ key.String(), &intType }
	default:
		panic("todo: implement")
	}

	return &exp, nil
}
