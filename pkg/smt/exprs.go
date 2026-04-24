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

type varDef struct {
	string
	SmtValue
}

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
			definedVars[def.string] = true
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

func (et *ExprTranslator) termToOperation(opTerm *ast.Term) (*Function,error) {
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

func (et *ExprTranslator) termToSmtValue(term *ast.Term) (*SmtValue, error) {
	switch v := term.Value.(type) {
	case ast.String:
		return NewSmtValueFromString(string(v)), nil
	case ast.Number:
		if val, ok := v.Int(); ok {
			return NewSmtValueFromInt(val), nil
		}
		return nil,verr.ErrInvalidInt(v.String())
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

func (et *ExprTranslator) arrayToSmt(arr *ast.Array) (*SmtValue, error) {
	tp, ok := et.TypeTrans.TypeInfo.Types[arr.String()]
	if !ok {
		return nil, verr.ErrTypeNotFound(arr.String())
	}

	depth := tp.TypeDepth()
	arrSmt := createConstArray("Int", depth)

	for index := range arr.Len() {
		val := arr.Elem(index)
		valSmt, err := et.termToSmtValue(val)
		if err != nil {
			return nil, err
		}
		valSmt = valSmt.WrapToDepth(depth - 1)
		arrSmt = fmt.Sprintf("(store %s %d %s)", arrSmt, index, valSmt.String())
	}

	return &SmtValue{
		value: fmt.Sprintf("(OArray%d %s)", depth, arrSmt),
		depth: depth,
	}, nil
}

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

func createConstArray(keyType string, depth int) string {
	undefChild := "OUndef"
	for d := range depth - 1 {
		undefChild = fmt.Sprintf("(Atom%d %s)", d+1, undefChild)
	}
	return fmt.Sprintf("((as const (Array %s OTypeD%d)) %s)", keyType, depth-1, undefChild)
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
	var path []string
	prefix := *et.packagePath
	if ref.HasPrefix(prefix) && len(prefix) != 0 {
		// Rule variable: <module-prefix>.<variable> ... e.g. data.test.foo
		name = removeQuotes(ref[len(prefix)].String())
		path = refToPath(ref[len(prefix)+1:])
	} else if len(ref) >= 2 && head == "input" {
		name = "input"
		path = refToPath(ref[1:])
	} else if len(ref) >= 2 && head == "data" && et.TypeTrans.TypeInfo.DataSchema != nil {
		dataPath := refToPath(ref[1:])
		// Only treat as a data schema reference if the path actually resolves through
		// Types["data"]. Rule variables appear as data.<module>.<variable> and are
		// not registered under the "data" object type.
		if dataTp, ok := et.TypeTrans.TypeInfo.Types["data"]; ok {
			if _, exists := dataTp.GetTypeFromPath(types.FromGroundPath(dataPath)); exists {
				name = "data"
				path = dataPath
			} else {
				return nil, verr.ErrTypeNotFound(ref.String())
			}
		}
	}

	tp, ok := et.TypeTrans.TypeInfo.Types[name]
	if !ok {
		return nil, verr.ErrTypeNotFound(name)
	}
	smtRef, actType, err := getSmtRef(name, path, &tp)
	if err != nil {
		return nil, err
	}
	// Return the raw OType expression without applying the atom extractor.
	// Extraction (num/str/bool) is deferred to the point of use (e.g. refToSmt
	// for operation arguments, or getVarValue for let-bound variable lookups).
	return &SmtValue{
		value:   smtRef,
		depth:   actType.TypeDepth(),
		atomics: getAtomicTypes(*actType),
	}, nil
}
