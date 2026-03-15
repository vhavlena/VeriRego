package smt

import (
	"github.com/open-policy-agent/opa/v1/ast"
	ast_types "github.com/open-policy-agent/opa/v1/types"
	types "github.com/vhavlena/verirego/pkg/types"
	verr "github.com/vhavlena/verirego/pkg/err"
)

type ArgType struct {
	depth  int
	atomic types.AtomicType
}

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
		depth: -1,	// FIXME might not be always -1
		atomic: at,
	}
}

type Function struct {
	smtName string
	args    []ArgType
	result  ArgType
}

func (f *Function) SmtCall(params []SmtValue) (*SmtValue,error) {
	if len(f.args) != len(params) {
		return nil, verr.ErrTypeNotFound // TODO: change error
	}

	callVal := "("
	callVal += f.smtName
	for i := range f.args {
		smt, err := params[i].AsArgType(f.args[i])
		if err != nil {
			return nil, verr.ErrTypeNotFound // TODO: change error
		}
		callVal += " "
		callVal += smt.String()
	}
	callVal += ")"

	atomics := []types.AtomicType{}
	if f.result.atomic != "" {
		atomics = append(atomics, f.result.atomic)
	}
	return &SmtValue{
		value: callVal,
		depth: f.result.depth,
		atomics: atomics,
		isConst: false,
	}, nil
}

func NewFunctionFromBuiltin(b *ast.Builtin, smtOp string) (string,Function) {
	bArgs := b.Decl.Args()
	args := make([]ArgType, 0)
	for _, arg := range bArgs {
		args = append(args, NewArgType(arg))
	}
	result := NewArgType(b.Decl.Result())
	// var smtName string
	// if smtOp != nil {
	// 	smtName = *smtOp
	// } else {
	// 	smtOp = &b.Infix
	// }
	return b.Name, Function{
		args: args,
		result: result,
		smtName: smtOp,
	}
}

func addBuiltin(funcMap map[string]Function, b ast.Builtin, smtOp string) {
	n, f := NewFunctionFromBuiltin(&b, smtOp)
	funcMap[n] = f
}

func GetBuiltinFuncMap() map[string]Function {
	funcMap := make(map[string]Function, 3)
	addBuiltin(funcMap, *ast.Plus,          "+")
	addBuiltin(funcMap, *ast.Minus,         "-")
	addBuiltin(funcMap, *ast.Multiply,      "*")
	addBuiltin(funcMap, *ast.Divide,        "/")
	addBuiltin(funcMap, *ast.Equal,         "=")
	addBuiltin(funcMap, *ast.Equality,      "=")
	// addBuiltin(funcMap, *ast.Assign, "=")
	addBuiltin(funcMap, *ast.GreaterThan,   ">")
	addBuiltin(funcMap, *ast.GreaterThanEq, ">=")
	addBuiltin(funcMap, *ast.LessThan,      "<")
	addBuiltin(funcMap, *ast.LessThanEq,    "<=")
	addBuiltin(funcMap, *ast.Concat,        "str.++")
	addBuiltin(funcMap, *ast.Contains,      "str.contains")
	addBuiltin(funcMap, *ast.StartsWith,    "str.prefixof")
	addBuiltin(funcMap, *ast.EndsWith,      "str.suffixof")
	addBuiltin(funcMap, *ast.IndexOf,       "str.indexof")
	addBuiltin(funcMap, *ast.Substring,     "str.substr")
	return funcMap
}

func argToType(arg Arg) ArgType {
	return ArgType {
		depth: arg.int,
	}
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
	return Function{ smtName: name, args: args, result: res }
}

