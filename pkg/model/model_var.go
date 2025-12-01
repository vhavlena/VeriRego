package model

import (
	"fmt"

	modelerr "github.com/vhavlena/verirego/pkg/err"
	z3 "github.com/vhavlena/z3-go/z3"
)

const errMissingModelValue = "model: variable %s has no value in model"

// ValueFromModelVar evaluates the named constant recorded in the context using
// ctx.ConstDecl and decodes it into a Value via ValueFromOTypeString.
//
// Parameters:
//
//	ctx *z3.Context: Context that records the constant declaration.
//	model *z3.Model: Model that provides the evaluated value.
//	varName string: Logical name of the constant to inspect.
//
// Returns:
//
//	Value: Decoded Go value for the requested constant.
//	error: Failure when the context/model are nil, the declaration is missing, or decoding fails.
func ValueFromModelVar(ctx *z3.Context, model *z3.Model, varName string) (Value, error) {
	if ctx == nil {
		return Value{}, modelerr.ErrNilZ3Context
	}
	if model == nil {
		return Value{}, modelerr.ErrNilZ3Model
	}
	varAst, ok := ctx.ConstDecl(varName)
	if !ok || varAst.String() == "" {
		return Value{}, modelerr.ErrMissingConstDecl(varName)
	}
	valueAst := model.Eval(varAst, true)
	if valueAst.Kind() == z3.ASTKindUnknown {
		return Value{}, fmt.Errorf(errMissingModelValue, varName)
	}
	return ValueFromOTypeString(valueAst)
}
