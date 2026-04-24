package smt

import (
	"fmt"

	"github.com/open-policy-agent/opa/v1/ast"
	ast_types "github.com/open-policy-agent/opa/v1/types"
	verr "github.com/vhavlena/verirego/pkg/err"
	types "github.com/vhavlena/verirego/pkg/types"
)

// ArgType is a structure holding information about function arguments
// It has depth specified separately, since for builtin functions, it should be -1
// For user-defined functions, it is primarily 0 (may be a subject to change)
type ArgType struct {
	depth  int
	atomic types.AtomicType
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
		depth: -1,
		atomic: at,
	}
}

type Function struct {
	name    string    // e.g., eq, plus
	args    []ArgType
	result  ArgType
	call    functionCall
}

type functionCall func(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue,error)

func mkSmtFunction(smtName string) functionCall {
	return func(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue,error) {
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
			value: callVal,
			depth: result.depth,
			atomics: atomics,
			isConst: false,
		}, nil
	}
}

func mkCompareFunction(op string) functionCall {
	return func(params []*SmtValue, _ []ArgType, _ ArgType) (*SmtValue,error) {
		if len(params) != 2 {
			return nil, verr.ErrUnexpectedParamCount("=", 2, len(params))
		}

		depth := max(params[0].GetDepth(), params[1].GetDepth())
		// TODO: check for undefined
		callVal := fmt.Sprintf("(%s %s %s)", op, params[0].WrapToDepth(depth).String(), params[1].WrapToDepth(depth).String())
		return &SmtValue{
			value: callVal,
			depth: -1,
			atomics: []types.AtomicType{types.AtomicBoolean},
		}, nil
	}
}

// SmtCall generates a SMT representation of call of given function
func (f *Function) SmtCall(params []*SmtValue) (*SmtValue,error) {
	return f.call(params, f.args, f.result)
}

func NewFunctionFromBuiltin(b *ast.Builtin, call functionCall) Function {
	bArgs := b.Decl.Args()
	args := make([]ArgType, 0)
	for _, arg := range bArgs {
		args = append(args, NewArgType(arg))
	}
	result := NewArgType(b.Decl.Result())
	return Function{
		args: args,
		result: result,
		name: b.Name,
		call: call,
	}
}

func addBuiltin(funcMap map[string]Function, b ast.Builtin, call functionCall) {
	f := NewFunctionFromBuiltin(&b, call)
	funcMap[f.name] = f
}

func GetBuiltinFuncMap() map[string]Function {
	funcMap := make(map[string]Function, 3)
	addBuiltin(funcMap, *ast.Plus,          mkSmtFunction("+"))
	addBuiltin(funcMap, *ast.Minus,         mkSmtFunction("-"))
	addBuiltin(funcMap, *ast.Multiply,      mkSmtFunction("*"))
	addBuiltin(funcMap, *ast.Divide,        mkSmtFunction("/"))
	addBuiltin(funcMap, *ast.GreaterThan,   mkSmtFunction(">"))
	addBuiltin(funcMap, *ast.GreaterThanEq, mkSmtFunction(">="))
	addBuiltin(funcMap, *ast.LessThan,      mkSmtFunction("<"))
	addBuiltin(funcMap, *ast.LessThanEq,    mkSmtFunction("<="))
	addBuiltin(funcMap, *ast.Concat,        mkSmtFunction("str.++"))
	addBuiltin(funcMap, *ast.Contains,      mkSmtFunction("str.contains"))
	addBuiltin(funcMap, *ast.StartsWith,    mkSmtFunction("str.prefixof"))
	addBuiltin(funcMap, *ast.EndsWith,      mkSmtFunction("str.suffixof"))
	addBuiltin(funcMap, *ast.IndexOf,       mkSmtFunction("str.indexof"))
	addBuiltin(funcMap, *ast.Substring,     mkSmtFunction("str.substr"))
	addBuiltin(funcMap, *ast.Equal,         mkCompareFunction("="))
	addBuiltin(funcMap, *ast.Equality,      mkCompareFunction("="))
	addBuiltin(funcMap, *ast.NotEqual,      mkCompareFunction("!="))
	return funcMap
}

func typeToArg(t types.RegoTypeDef) ArgType {
	return ArgType{
		depth: t.TypeDepth(),
		atomic: t.AtomicType,
	}
}

func NewFunction(name string, tp types.RegoTypeDef) Function {
	args := make([]ArgType, len(tp.FunctionDef.ParamTypes))
	for i,p := range tp.FunctionDef.ParamTypes {
		args[i] = typeToArg(p)
	}
	res := typeToArg(tp.FunctionDef.ReturnType)
	call := mkSmtFunction(name)
	return Function{ name: name, args: args, result: res, call: call }
}

