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

	atomSort, atomDecls := ctx.MkDatatype("OTypeD0", []*z3.Constructor{stringCtor, numberCtor, booleanCtor, nullCtor, undefCtor})

	return &oTypeEnv{
		sort:        atomSort,
		atomCtor:    z3.FuncDecl{},
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
	return ctx.App(e.stringCtor, ctx.StringVal(v))
}

func (e *oTypeEnv) atomFromBool(ctx *z3.Context, v bool) z3.AST {
	return ctx.App(e.booleanCtor, ctx.BoolVal(v))
}

func (e *oTypeEnv) atomFromInt(ctx *z3.Context, v int64) z3.AST {
	return ctx.App(e.numberCtor, ctx.IntVal(v))
}

const otypeSortsScript = `
(declare-datatypes ()
	((OTypeD0
		(OString (str String))
		(ONumber (num Int))
		(OBoolean (bool Bool))
		ONull
		OUndef))
)

(declare-datatypes ()
  ((OTypeD1
    (Atom1 (atom1 OTypeD0))
	(OObj1 (obj1 (Array String OTypeD0)))
	(OArray1 (arr1 (Array Int OTypeD0)))
  ))
)

`

const otypeSortsScriptD2 = otypeSortsScript + `
(declare-datatypes ()
	((OTypeD2
		(Atom2 (atom2 OTypeD1))
		(OObj2 (obj2 (Array String OTypeD1)))
		(OArray2 (arr2 (Array Int OTypeD1)))
	))
)
`

const smtObjectScript = otypeSortsScript + `

(declare-fun x () OTypeD1)
(assert (is-OObj1 x))
(assert (is-OString (select (obj1 x) "a")))
`

const smtObjectMultiFieldScript = otypeSortsScript + `

(declare-fun x () OTypeD1)
(assert (is-OObj1 x))
(assert (is-OString (select (obj1 x) "b")))
(assert (is-OString (select (obj1 x) "c")))
(assert (is-ONumber (select (obj1 x) "d")))
`

const smtObjectFromStoreLeavesScript = otypeSortsScript + `

(declare-fun x () OTypeD1)
(declare-fun leaf_a () OTypeD0)
(declare-fun leaf_b () OTypeD0)
(declare-fun leaf_c () OTypeD0)

(assert (is-OString leaf_a))
(assert (is-ONumber leaf_b))
(assert (is-OBoolean leaf_c))

(assert (= x (OObj1 (store (store (store ((as const (Array String OTypeD0)) OUndef) "a" leaf_a) "b" leaf_b) "c" leaf_c))))
`

const smtNestedObjectFromStoreLeavesD2Script = otypeSortsScriptD2 + `

(declare-fun x () OTypeD2)
(declare-fun leaf_flag () OTypeD0)
(declare-fun leaf_a () OTypeD0)
(declare-fun leaf_b () OTypeD0)

(assert (is-OBoolean leaf_flag))
(assert (is-OString leaf_a))
(assert (is-ONumber leaf_b))

(assert (= x
	(OObj2
		(store
			(store ((as const (Array String OTypeD1)) (Atom1 OUndef))
						 "flag" (Atom1 leaf_flag))
			"outer"
			(OObj1
				(store
					(store ((as const (Array String OTypeD0)) OUndef) "a" leaf_a)
					"b" leaf_b))))))
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
	expected := NewMapValue(map[string]Value{
		"a": NewStringValue("a"),
	})
	if !val.Equal(&expected) {
		t.Fatalf("decoded value mismatch: got %#v, want %#v", val.AsInterface(), expected.AsInterface())
	}
}

func TestValueFromModelVar_FromSMTLIBScriptWithFields(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	solver := ctx.NewSolver()
	defer solver.Close()

	if err := solver.AssertSMTLIB2String(smtObjectMultiFieldScript); err != nil {
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
	expected := NewMapValue(map[string]Value{
		"b": NewStringValue("b"),
		"c": NewStringValue("c"),
		"d": NewIntValue(2),
	})
	if !val.Equal(&expected) {
		t.Fatalf("decoded value mismatch: got %#v, want %#v", val.AsInterface(), expected.AsInterface())
	}
}

func TestValueFromModelVar_FromSMTLIBStoreLeavesFormula(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	solver := ctx.NewSolver()
	defer solver.Close()

	if err := solver.AssertSMTLIB2String(smtObjectFromStoreLeavesScript); err != nil {
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

	got, ok := val.Map()
	if !ok {
		t.Fatalf("expected map payload")
	}
	if len(got) != 3 {
		t.Fatalf("expected 3 keys (a,b,c), got %d: %#v", len(got), val.AsInterface())
	}
	for _, k := range []string{"a", "b", "c"} {
		if _, exists := got[k]; !exists {
			t.Fatalf("missing expected key %q in decoded object: %#v", k, val.AsInterface())
		}
	}
}

func TestValueFromModelVar_FromSMTLIBNestedStoreLeavesFormula_D2(t *testing.T) {
	ctx := z3.NewContext(nil)
	if ctx == nil {
		t.Fatalf("failed to allocate z3 context")
	}
	defer ctx.Close()

	solver := ctx.NewSolver()
	defer solver.Close()

	if err := solver.AssertSMTLIB2String(smtNestedObjectFromStoreLeavesD2Script); err != nil {
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

	root, ok := val.Map()
	if !ok {
		t.Fatalf("expected map payload")
	}
	if _, exists := root["flag"]; !exists {
		t.Fatalf("missing expected key %q in decoded object: %#v", "flag", val.AsInterface())
	}
	if _, exists := root["outer"]; !exists {
		t.Fatalf("missing expected key %q in decoded object: %#v", "outer", val.AsInterface())
	}

	flagVal := root["flag"]
	if flagVal.Kind() != ValueBool {
		t.Fatalf("expected flag to be bool, got %s: %#v", flagVal.Kind(), flagVal.AsInterface())
	}

	outerVal := root["outer"]
	if outerVal.Kind() != ValueMap {
		t.Fatalf("expected outer to be map, got %s: %#v", outerVal.Kind(), outerVal.AsInterface())
	}
	outer, _ := outerVal.Map()
	if _, exists := outer["a"]; !exists {
		t.Fatalf("missing expected key %q in decoded outer: %#v", "a", outerVal.AsInterface())
	}
	if _, exists := outer["b"]; !exists {
		t.Fatalf("missing expected key %q in decoded outer: %#v", "b", outerVal.AsInterface())
	}
	aVal := outer["a"]
	if aVal.Kind() != ValueString {
		t.Fatalf("expected outer.a to be string, got %s: %#v", aVal.Kind(), aVal.AsInterface())
	}
	bVal := outer["b"]
	if bVal.Kind() != ValueInt {
		t.Fatalf("expected outer.b to be int, got %s: %#v", bVal.Kind(), bVal.AsInterface())
	}
}

func TestValueEqual_MapWildcards(t *testing.T) {
	cases := []struct {
		name  string
		left  map[string]Value
		right map[string]Value
		want  bool
	}{
		{
			name: "identicalWildcards",
			left: map[string]Value{
				"*": NewIntValue(2),
			},
			right: map[string]Value{
				"*": NewIntValue(2),
			},
			want: true,
		},
		{
			name: "wildcardSatisfiesExplicitKeys",
			left: map[string]Value{
				"*": NewStringValue("x"),
			},
			right: map[string]Value{
				"foo": NewStringValue("x"),
				"bar": NewStringValue("x"),
			},
			want: true,
		},
		{
			name: "explicitOverridesWildcard",
			left: map[string]Value{
				"foo": NewIntValue(3),
				"*":   NewIntValue(1),
			},
			right: map[string]Value{
				"foo": NewIntValue(3),
				"bar": NewIntValue(1),
			},
			want: true,
		},
		{
			name: "wildcardValueMismatch",
			left: map[string]Value{
				"*": NewIntValue(1),
			},
			right: map[string]Value{
				"*": NewIntValue(2),
			},
			want: false,
		},
		{
			name: "explicitValueMismatch",
			left: map[string]Value{
				"*": NewIntValue(1),
			},
			right: map[string]Value{
				"foo": NewIntValue(2),
			},
			want: false,
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			leftVal := NewMapValue(tc.left)
			rightVal := NewMapValue(tc.right)
			if got := leftVal.Equal(&rightVal); got != tc.want {
				t.Fatalf("left.Equal(right) = %v, want %v", got, tc.want)
			}
			if got := rightVal.Equal(&leftVal); got != tc.want {
				t.Fatalf("right.Equal(left) = %v, want %v", got, tc.want)
			}
		})
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
