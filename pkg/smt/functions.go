package smt

import (
	"github.com/open-policy-agent/opa/v1/ast"
	ast_types "github.com/open-policy-agent/opa/v1/types"
	verr "github.com/vhavlena/verirego/pkg/err"
	types "github.com/vhavlena/verirego/pkg/types"
)

// seqArgDepth is a sentinel depth value that marks an argument as having the
// SMT sort (Seq String) rather than one of the standard OTypeD<n> sorts.
const seqArgDepth = -10

// ArgType is a structure holding information about function arguments
// It has depth specified separately, since for builtin functions, it should be -1
// For user-defined functions, it is primarily 0 (may be a subject to change)
type ArgType struct {
	depth  int
	atomic types.AtomicType
}

// Arg represents a named argument, which is used for function definitions.
type Arg struct {
	name string
	typ  ArgType
}

func NewArg(name string, tp types.RegoTypeDef) Arg {
	return Arg{
		name: name,
		typ:  newArgTypeFromTypeDef(tp),
	}
}

// newPathArg creates an Arg for the path parameter (sort: Seq OTypeD0).
func newPathArg(name string) Arg {
	return Arg{name: name, typ: ArgType{depth: seqArgDepth}}
}

// transformType maps Rego ast Type into intermediate AtomicType
func transformType(t ast_types.Type) types.AtomicType {
	switch x := t.(type) {
	case ast_types.Boolean:
		return types.AtomicBoolean
	case ast_types.Number:
		return types.AtomicInt
	case ast_types.Null:
		return types.AtomicNull
	case ast_types.String:
		return types.AtomicString
	case ast_types.Any:
		var atomic types.AtomicType
		for _, t := range x {
			at := transformType(t)
			if at != "" {
				if atomic != "" {
					return ""
				} else {
					atomic = at
				}
			}
		}
		return atomic
	default:
		return ""
	}
}

func NewArgType(t ast_types.Type) ArgType {
	at := transformType(t)
	return ArgType{
		depth:  -1,
		atomic: at,
	}
}

// Function is a structure for handling the conversion of Rego functions into SMT.
type Function struct {
	name   string // for example: eq, plus, ...
	args   []ArgType
	result ArgType // the return type
	call   callFn  // function for creating the SMT representation of call, w.r.t. the given arguments
}

type callFn func(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue, error)

// mkSmtFunction creates a callFn function,
// which checks the expected parameter types and creates a SMT value
// of the form "(smtName par1 par2 ...)"
func mkSmtFunction(smtName string) callFn {
	return func(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue, error) {
		if len(args) != len(params) {
			return nil, verr.ErrUnexpected
		}

		callVal := "("
		callVal += smtName
		for i := range args {
			smt, err := params[i].AsArgType(args[i])
			if err != nil {
				return nil, verr.ErrUnexpectedValueType(params[i].String(), string(args[i].atomic))
			}
			callVal += " "
			callVal += smt.String()
		}
		callVal += ")"

		atomics := []types.AtomicType{}
		if result.atomic != "" {
			atomics = append(atomics, result.atomic)
		}
		return &SmtValue{
			value:   callVal,
			depth:   result.depth,
			atomics: atomics,
			isConst: false,
		}, nil
	}
}

// EqFunction checks the equality of its two parameters.
func EqFunction(params []*SmtValue, _ []ArgType, _ ArgType) (*SmtValue, error) {
	if len(params) != 2 {
		return nil, verr.ErrUnexpectedParamCount("=", 2, len(params))
	}

	p1 := params[0]
	p2 := params[1]
	eq := p1.Equals(p2)
	return eq.IntoValue(), nil
}

// NeqFunction checks the inequality of its two parameters.
func NeqFunction(params []*SmtValue, _ []ArgType, _ ArgType) (*SmtValue, error) {
	if len(params) != 2 {
		return nil, verr.ErrUnexpectedParamCount("!=", 2, len(params))
	}

	p1 := params[0]
	p2 := params[1]
	eq := p1.Equals(p2)
	return eq.Not().IntoValue(), nil
}

// SmtCall generates a SMT representation of call of given function
func (f *Function) SmtCall(params []*SmtValue) (*SmtValue, error) {
	return f.call(params, f.args, f.result)
}

func NewFunctionFromBuiltin(b *ast.Builtin, call callFn) Function {
	bArgs := b.Decl.Args()
	args := make([]ArgType, 0)
	for _, arg := range bArgs {
		args = append(args, NewArgType(arg))
	}
	result := NewArgType(b.Decl.Result())
	return Function{
		args:   args,
		result: result,
		name:   b.Name,
		call:   call,
	}
}

// addBuiltin converts given Builtin into Function and puts it in the funcMap.
func addBuiltin(funcMap map[string]Function, b ast.Builtin, call callFn) {
	f := NewFunctionFromBuiltin(&b, call)
	funcMap[f.name] = f
}

// addNumericCompare registers a binary comparison operator that takes two integer
// arguments and returns a boolean. This overrides OPA's "any any" arg types with
// explicit AtomicInt args so that SMT generation correctly unwraps OTypeD0 values.
func addNumericCompare(funcMap map[string]Function, b ast.Builtin, smtOp string) {
	intArg := ArgType{depth: -1, atomic: types.AtomicInt}
	boolResult := ArgType{depth: -1, atomic: types.AtomicBoolean}
	funcMap[b.Name] = Function{
		name:   b.Name,
		args:   []ArgType{intArg, intArg},
		result: boolResult,
		call:   mkSmtFunction(smtOp),
	}
}

// GetBuiltinFuncMap constructs and returns a map of Rego function converters into SMT.
// This map is accessed via the names of functions, e.g., "plus", "eq".
func GetBuiltinFuncMap() map[string]Function {
	funcMap := make(map[string]Function, 17)
	addBuiltin(funcMap, *ast.Plus, mkSmtFunction("+"))
	addBuiltin(funcMap, *ast.Minus, mkSmtFunction("-"))
	addBuiltin(funcMap, *ast.Multiply, mkSmtFunction("*"))
	addBuiltin(funcMap, *ast.Divide, mkSmtFunction("/"))
	addNumericCompare(funcMap, *ast.GreaterThan, ">")
	addNumericCompare(funcMap, *ast.GreaterThanEq, ">=")
	addNumericCompare(funcMap, *ast.LessThan, "<")
	addNumericCompare(funcMap, *ast.LessThanEq, "<=")
	addBuiltin(funcMap, *ast.Concat, mkSmtFunction("str.++"))
	addBuiltin(funcMap, *ast.Contains, mkSmtFunction("str.contains"))
	addBuiltin(funcMap, *ast.StartsWith, mkSmtFunction("str.prefixof"))
	addBuiltin(funcMap, *ast.EndsWith, mkSmtFunction("str.suffixof"))
	addBuiltin(funcMap, *ast.IndexOf, mkSmtFunction("str.indexof"))
	addBuiltin(funcMap, *ast.Substring, mkSmtFunction("str.substr"))
	addBuiltin(funcMap, *ast.Equal, EqFunction)
	addBuiltin(funcMap, *ast.Equality, EqFunction)
	addBuiltin(funcMap, *ast.NotEqual, NeqFunction)
	return funcMap
}

// newArgTypeFromTypeDef transforms RegoTypeDef into ArgType.
func newArgTypeFromTypeDef(t types.RegoTypeDef) ArgType {
	if t.Kind == types.KindSeq {
		return ArgType{depth: seqArgDepth}
	}
	return ArgType{
		depth:  t.TypeDepth(),
		atomic: t.AtomicType,
	}
}

// NewFunction notes a user-defined function name of type tp.
func NewFunction(name string, tp types.RegoTypeDef) Function {
	if tp.FunctionDef == nil {
		panic("function type expected")
	}
	args := make([]ArgType, len(tp.FunctionDef.ParamTypes))
	for i, p := range tp.FunctionDef.ParamTypes {
		args[i] = newArgTypeFromTypeDef(p)
	}
	res := newArgTypeFromTypeDef(tp.FunctionDef.ReturnType)
	call := mkSmtFunction(name)
	return Function{name: name, args: args, result: res, call: call}
}
