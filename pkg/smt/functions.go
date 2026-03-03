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

func NewArgType(t ast_types.Type) ArgType {
	switch t.(type) {
	case ast_types.Boolean:
		return ArgType{
			depth: -1,
			atomic: types.AtomicBoolean,
		}
	case ast_types.Number:
		return ArgType{
			depth: -1,
			atomic: types.AtomicInt,
		}
	case ast_types.Null:
		return ArgType{
			depth: -1,
			atomic: types.AtomicNull,
		}
	case ast_types.String:
		return ArgType{
			depth: -1,
			atomic: types.AtomicString,
		}
	case ast_types.Any:
		return ArgType{
			depth: -1,
		}
	}
	panic("Unreachable")
}

type Function struct {
	smtName string
	args    []ArgType
	result  ArgType
}

func NewFunctionFromBuiltin(b *ast.Builtin) Function {
	bArgs := b.Decl.Args()
	args := make([]ArgType, len(bArgs))
	for _, arg := range bArgs {
		args = append(args, NewArgType(arg))
	}
	result := NewArgType(b.Decl.Result())
	return Function{
		args: args,
		result: result,
	}
}
