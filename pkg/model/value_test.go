package model

import (
	"testing"

	z3 "github.com/vhavlena/z3-go/z3"
)

type oTypeEnv struct {
	sort        z3.Sort
	atomCtor    z3.FuncDecl
	stringCtor  z3.FuncDecl
	numberCtor  z3.FuncDecl
	booleanCtor z3.FuncDecl
}

func newOTypeEnv(ctx *z3.Context) (*oTypeEnv, error) {
	stringCtor := ctx.MkConstructor("OString", "is-OString", []z3.ADTField{{Name: "str", Sort: ctx.StringSort()}})
	numberCtor := ctx.MkConstructor("ONumber", "is-ONumber", []z3.ADTField{{Name: "num", Sort: ctx.IntSort()}})
	booleanCtor := ctx.MkConstructor("OBoolean", "is-OBoolean", []z3.ADTField{{Name: "bool", Sort: ctx.BoolSort()}})
	nullCtor := ctx.MkConstructor("ONull", "is-ONull", nil)
	undefCtor := ctx.MkConstructor("OUndef", "is-OUndef", nil)

	atomSort, atomDecls := ctx.MkDatatype("OAtom", []*z3.Constructor{stringCtor, numberCtor, booleanCtor, nullCtor, undefCtor})
	atomCtor := ctx.MkConstructor("Atom", "is-Atom", []z3.ADTField{{Name: "atom", Sort: atomSort}})
	genTypeSort, genDecls := ctx.MkDatatype("OGenTypeAtom", []*z3.Constructor{atomCtor})

	return &oTypeEnv{
		sort:        genTypeSort,
		atomCtor:    genDecls[0].Constructor,
		stringCtor:  atomDecls[0].Constructor,
		numberCtor:  atomDecls[1].Constructor,
		booleanCtor: atomDecls[2].Constructor,
	}, nil
}

func mustNewOTypeEnv(t *testing.T, ctx *z3.Context) *oTypeEnv {
	t.Helper()
	env, err := newOTypeEnv(ctx)
	if err != nil {
		t.Fatalf("newOTypeEnv error: %v", err)
	}
	return env
}

func (e *oTypeEnv) atomFromString(ctx *z3.Context, v string) z3.AST {
	return ctx.App(e.atomCtor, ctx.App(e.stringCtor, ctx.StringVal(v)))
}

func (e *oTypeEnv) atomFromBool(ctx *z3.Context, v bool) z3.AST {
	return ctx.App(e.atomCtor, ctx.App(e.booleanCtor, ctx.BoolVal(v)))
}

func (e *oTypeEnv) atomFromInt(ctx *z3.Context, v int64) z3.AST {
	return ctx.App(e.atomCtor, ctx.App(e.numberCtor, ctx.IntVal(v)))
}

const smtObjectScript = `
(declare-datatypes ()
	((OAtom
		(OString (str String))
		(ONumber (num Int))
		(OBoolean (bool Bool))
		ONull
		OUndef))
)

(declare-datatypes (T)
	((OGenType
		(Atom (atom OAtom))
		(OObj (obj (Array String T)))
		(OArray (arr (Array Int T)))))
)

(declare-datatypes ()
	((OGenTypeAtom (Atom (atom OAtom))))
)

(define-sort OTypeD0 () (OGenType OGenTypeAtom))

(declare-fun x () OTypeD0)
(assert (is-OObj x))
(assert (is-OString (atom (select (obj x) "a"))))
`

func TestValueFromSimpleAST_StringViaModel(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	env := mustNewOTypeEnv(t, ctx)
	solver := ctx.NewSolver()
	defer solver.Close()

	strVar := ctx.Const("str_val", env.sort)
	solver.Assert(z3.Eq(strVar, env.atomFromString(ctx, "hello world")))

	model := checkModel(t, solver)
	defer model.Close()

	val, err := ValueFromModelVar(ctx, model, "str_val")
	if err != nil {
		t.Fatalf("ValueFromModelVar error: %v", err)
	}
	if val.Kind() != ValueString {
		t.Fatalf("expected ValueString kind, got %s", val.Kind())
	}
	got, ok := val.String()
	if !ok || got != "hello world" {
		t.Fatalf("unexpected string payload: %q (ok=%v)", got, ok)
	}
	if iface := val.AsInterface(); iface != "hello world" {
		t.Fatalf("unexpected interface value: %#v", iface)
	}
}

func TestValueFromSimpleAST_BoolViaModel(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	env := mustNewOTypeEnv(t, ctx)
	solver := ctx.NewSolver()
	defer solver.Close()

	boolVar := ctx.Const("bool_val", env.sort)
	solver.Assert(z3.Eq(boolVar, env.atomFromBool(ctx, true)))

	model := checkModel(t, solver)
	defer model.Close()

	val, err := ValueFromModelVar(ctx, model, "bool_val")
	if err != nil {
		t.Fatalf("ValueFromModelVar error: %v", err)
	}
	if val.Kind() != ValueBool {
		t.Fatalf("expected ValueBool kind, got %s", val.Kind())
	}
	got, ok := val.Bool()
	if !ok || !got {
		t.Fatalf("unexpected bool payload: %v (ok=%v)", got, ok)
	}
	if iface := val.AsInterface(); iface != true {
		t.Fatalf("unexpected interface value: %#v", iface)
	}
}

func TestValueFromSimpleAST_IntViaModel(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	env := mustNewOTypeEnv(t, ctx)
	solver := ctx.NewSolver()
	defer solver.Close()

	intVar := ctx.Const("int_val", env.sort)
	solver.Assert(z3.Eq(intVar, env.atomFromInt(ctx, 42)))

	model := checkModel(t, solver)
	defer model.Close()

	val, err := ValueFromModelVar(ctx, model, "int_val")
	if err != nil {
		t.Fatalf("ValueFromModelVar error: %v", err)
	}
	if val.Kind() != ValueInt {
		t.Fatalf("expected ValueInt kind, got %s", val.Kind())
	}
	got, ok := val.Int64()
	if !ok || got != 42 {
		t.Fatalf("unexpected int payload: %d (ok=%v)", got, ok)
	}
	if iface := val.AsInterface(); iface != int64(42) {
		t.Fatalf("unexpected interface value: %#v", iface)
	}
}

func TestValueFromModelVar_FromSMTLIBScript(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	solver := ctx.NewSolver()
	defer solver.Close()

	if err := solver.AssertSMTLIB2String(smtObjectScript); err != nil {
		t.Fatalf("AssertSMTLIB2String error: %v", err)
	}

	model := checkModel(t, solver)
	defer model.Close()

	val, err := ValueFromModelVar(ctx, model, "x")
	if err != nil {
		t.Fatalf("ValueFromModelVar error: %v", err)
	}
	if val.Kind() != ValueMap {
		t.Fatalf("expected ValueMap kind, got %s", val.Kind())
	}
	fields, ok := val.Map()
	if !ok {
		t.Fatalf("expected map payload")
	}
	fieldVal, exists := fields["*"]
	if !exists {
		t.Fatalf("expected key '*' in decoded object")
	}
	if fieldVal.Kind() != ValueString {
		t.Fatalf("expected string kind for field '*', got %s", fieldVal.Kind())
	}
	str, ok := fieldVal.String()
	if !ok || str != "a" {
		t.Fatalf("unexpected string payload for key '*': %q (ok=%v)", str, ok)
	}
}

func checkModel(t *testing.T, solver *z3.Solver) *z3.Model {
	t.Helper()
	res, err := solver.Check()
	if err != nil {
		t.Fatalf("solver.Check error: %v", err)
	}
	if res != z3.Sat {
		t.Fatalf("expected SAT, got %v", res)
	}
	model := solver.Model()
	if model == nil {
		t.Fatalf("solver produced nil model")
	}
	return model
}
