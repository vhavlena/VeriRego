package smt

import (
	"strings"
	"testing"

	"github.com/vhavlena/verirego/pkg/types"
)

func cmdStrings(cmds []*SmtCommand) []string {
	out := make([]string, 0, len(cmds))
	for _, c := range cmds {
		out = append(out, c.String())
	}
	return out
}

func TestTypeDefs_getSmtConstr_AtomicString(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	typeDef := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicString,
	}
	b, err := td.getSmtConstr("x", typeDef)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(b.Props) != 1 || b.Props[0].String() != "(is-OString x)" {
		t.Errorf("unexpected constraint: %v", b.Props)
	}
}

func TestTypeDefs_getSmtConstr_AtomicInt(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	typeDef := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicInt,
	}
	b, err := td.getSmtConstr("y", typeDef)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(b.Props) != 1 || b.Props[0].String() != "(is-ONumber y)" {
		t.Errorf("unexpected constraint: %v", b.Props)
	}
}

func TestTypeDefs_getSmtConstr_Object(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	objType := &types.RegoTypeDef{
		Kind: types.KindObject,
		ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
			"foo": {
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicString,
			},
			"bar": {
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicInt,
			},
			"baz": {
				Kind: types.KindObject,
				ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
					"x": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicBoolean,
					},
				}, false),
			},
		}, false),
	}
	b, err := td.getSmtConstr("z", objType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := map[string]bool{
		"(is-OObj2 z)":                         false,
		"(is-OObj1 (select (obj2 z) \"baz\"))": false,
	}
	atomicChecks := map[string]bool{
		"(is-OString (select (obj2 z) \"foo\"))":                        false,
		"(is-ONumber (select (obj2 z) \"bar\"))":                        false,
		"(is-OBoolean (select (obj1 (select (obj2 z) \"baz\")) \"x\"))": false,
	}
	for _, c := range b.Props {
		cs := c.String()
		if _, ok := want[cs]; ok {
			want[cs] = true
		}
		if _, ok := atomicChecks[cs]; ok {
			atomicChecks[cs] = true
		}
	}
	for k, v := range want {
		if !v {
			t.Errorf("missing expected object type constraint: %s", k)
		}
	}
	for k, v := range atomicChecks {
		if !v {
			t.Errorf("missing expected atomic constraint: %s", k)
		}
	}
}

func TestTypeDefs_getSmtConstr_NestedObject(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	nestedType := &types.RegoTypeDef{
		Kind: types.KindObject,
		ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
			"outer": {
				Kind: types.KindObject,
				ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
					"inner": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicString,
					},
					"num": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicInt,
					},
				}, false),
			},
			"flag": {
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicBoolean,
			},
		}, false),
	}
	b, err := td.getSmtConstr("n", nestedType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := map[string]bool{
		"(is-OObj2 n)":                           false,
		"(is-OObj1 (select (obj2 n) \"outer\"))": false,
	}
	atomicChecks := map[string]bool{
		"(is-OBoolean (select (obj2 n) \"flag\"))":                           false,
		"(is-OString (select (obj1 (select (obj2 n) \"outer\")) \"inner\"))": false,
		"(is-ONumber (select (obj1 (select (obj2 n) \"outer\")) \"num\"))":   false,
	}
	for _, c := range b.Props {
		cs := c.String()
		if _, ok := want[cs]; ok {
			want[cs] = true
		}
		if _, ok := atomicChecks[cs]; ok {
			atomicChecks[cs] = true
		}
	}
	for k, v := range want {
		if !v {
			t.Errorf("missing expected nested object type constraint: %s", k)
		}
	}
	for k, v := range atomicChecks {
		if !v {
			t.Errorf("missing expected nested atomic constraint: %s", k)
		}
	}
}

func TestTypeDefs_getSmtConstr_UnsupportedType(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	unknownType := &types.RegoTypeDef{Kind: types.KindUnknown}
	_, err := td.getSmtConstr("v", unknownType)
	if err == nil {
		t.Error("expected error for unsupported type, got nil")
	}
}

func TestTypeDefs_getSmtConstr_UnsupportedAtomic(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	badAtomic := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: "invalid-atomic-type", // invalid atomic type
	}
	_, err := td.getSmtConstr("w", badAtomic)
	if err == nil {
		t.Error("expected error for unsupported atomic type, got nil")
	}
}

func TestTypeDefs_getSmtConstrAssert_NestedObject(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	nestedType := &types.RegoTypeDef{
		Kind: types.KindObject,
		ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
			"outer": {
				Kind: types.KindObject,
				ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
					"inner": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicString,
					},
					"num": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicInt,
					},
				}, false),
			},
			"flag": {
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicBoolean,
			},
		}, false),
	}
	b, err := td.getSmtConstrAssert("n", nestedType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if b == nil || len(b.Asserts) != 1 {
		t.Fatalf("expected exactly one assert, got: %#v", b)
	}
	assertStr := b.Asserts[0].String()
	checks := []string{
		"(is-OObj2 n)",
		"(is-OObj1 (select (obj2 n) \"outer\"))",
		"(is-OBoolean (select (obj2 n) \"flag\"))",
		"(is-OString (select (obj1 (select (obj2 n) \"outer\")) \"inner\"))",
		"(is-ONumber (select (obj1 (select (obj2 n) \"outer\")) \"num\"))",
	}
	for _, c := range checks {
		if !strings.Contains(assertStr, c) {
			t.Errorf("assertion missing expected constraint: %s", c)
		}
	}
	if !strings.HasPrefix(assertStr, "(assert (and ") || !strings.HasSuffix(assertStr, "))") {
		t.Errorf("assertion does not have expected SMT-LIB format: %s", assertStr)
	}
}

func TestTypeDefs_getSmtArrConstr(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}

	// Test simple array of atomic strings
	arrType := &types.RegoTypeDef{
		Kind: types.KindArray,
		ArrayType: &types.RegoTypeDef{
			Kind:       types.KindAtomic,
			AtomicType: types.AtomicString,
		},
	}
	b, err := td.getSmtArrConstr("a", arrType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(b.Props) != 2 {
		t.Errorf("expected 2 constraints, got %d", len(b.Props))
	}
	if b.Props[0].String() != "(is-OArray1 a)" {
		t.Errorf("missing or incorrect OArray constraint: %v", b.Props[0].String())
	}
	if !strings.Contains(b.Props[1].String(), "(is-OString elem)") {
		t.Errorf("missing or incorrect atomic string constraint in forall: %v", b.Props[1].String())
	}

	// Test nested array: array of array of ints
	nestedArrType := &types.RegoTypeDef{
		Kind: types.KindArray,
		ArrayType: &types.RegoTypeDef{
			Kind: types.KindArray,
			ArrayType: &types.RegoTypeDef{
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicInt,
			},
		},
	}
	nestedB, err := td.getSmtArrConstr("b", nestedArrType)
	if err != nil {
		t.Fatalf("unexpected error for nested array: %v", err)
	}
	if len(nestedB.Props) != 2 {
		t.Errorf("expected 2 constraints for nested array, got %d", len(nestedB.Props))
	}
	if nestedB.Props[0].String() != "(is-OArray2 b)" {
		t.Errorf("missing or incorrect OArray constraint for nested array: %v", nestedB.Props[0].String())
	}
	if !strings.Contains(nestedB.Props[1].String(), "(is-OArray1 elem)") {
		t.Errorf("missing or incorrect nested OArray constraint in forall: %v", nestedB.Props[1].String())
	}
	if !strings.Contains(nestedB.Props[1].String(), "(is-ONumber elem") {
		t.Errorf("missing or incorrect atomic int constraint in nested forall: %v", nestedB.Props[1].String())
	}
}

func TestTypeDefs_getSmtConstr_Union(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}

	// Test simple union: string | int
	simpleUnionType := &types.RegoTypeDef{
		Kind: types.KindUnion,
		Union: []types.RegoTypeDef{
			{Kind: types.KindAtomic, AtomicType: types.AtomicString},
			{Kind: types.KindAtomic, AtomicType: types.AtomicInt},
		},
	}
	b, err := td.getSmtConstr("u", simpleUnionType)
	if err != nil {
		t.Fatalf("unexpected error for simple union: %v", err)
	}
	if len(b.Props) != 1 {
		t.Errorf("expected 1 constraint for simple union, got %d", len(b.Props))
	}
	if !strings.Contains(b.Props[0].String(), "(or ") {
		t.Errorf("union constraint should contain 'or': %v", b.Props[0].String())
	}
	if !strings.Contains(b.Props[0].String(), "(is-OString u)") {
		t.Errorf("missing string constraint in union: %v", b.Props[0].String())
	}
	if !strings.Contains(b.Props[0].String(), "(is-ONumber u)") {
		t.Errorf("missing int constraint in union: %v", b.Props[0].String())
	}

	// Test complex union: string | object | array
	complexUnionType := &types.RegoTypeDef{
		Kind: types.KindUnion,
		Union: []types.RegoTypeDef{
			{Kind: types.KindAtomic, AtomicType: types.AtomicString},
			{
				Kind: types.KindObject,
				ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
					"field1": {Kind: types.KindAtomic, AtomicType: types.AtomicBoolean},
				}, false),
			},
			{
				Kind:      types.KindArray,
				ArrayType: &types.RegoTypeDef{Kind: types.KindAtomic, AtomicType: types.AtomicInt},
			},
		},
	}
	b, err = td.getSmtConstr("v", complexUnionType)
	if err != nil {
		t.Fatalf("unexpected error for complex union: %v", err)
	}
	if len(b.Props) != 1 {
		t.Errorf("expected 1 constraint for complex union, got %d", len(b.Props))
	}
	complexConstraintStr := b.Props[0].String()
	if !strings.Contains(complexConstraintStr, "(or ") {
		t.Errorf("complex union constraint should contain 'or': %v", complexConstraintStr)
	}
	if !strings.Contains(complexConstraintStr, "(is-OString v)") {
		t.Errorf("missing string constraint in complex union: %v", complexConstraintStr)
	}
	if !strings.Contains(complexConstraintStr, "(is-OBoolean (select (obj1 v) \"field1\"))") {
		t.Errorf("missing object field constraint in complex union: %v", complexConstraintStr)
	}
	if !strings.Contains(complexConstraintStr, "(is-OArray1 v)") {
		t.Errorf("missing array constraint in complex union: %v", complexConstraintStr)
	}

	// Test nested union: (string | int) | boolean
	nestedUnionType := &types.RegoTypeDef{
		Kind: types.KindUnion,
		Union: []types.RegoTypeDef{
			{
				Kind: types.KindUnion,
				Union: []types.RegoTypeDef{
					{Kind: types.KindAtomic, AtomicType: types.AtomicString},
					{Kind: types.KindAtomic, AtomicType: types.AtomicInt},
				},
			},
			{Kind: types.KindAtomic, AtomicType: types.AtomicBoolean},
		},
	}
	b, err = td.getSmtConstr("w", nestedUnionType)
	if err != nil {
		t.Fatalf("unexpected error for nested union: %v", err)
	}
	if len(b.Props) != 1 {
		t.Errorf("expected 1 constraint for nested union, got %d", len(b.Props))
	}
	nestedConstraintStr := b.Props[0].String()
	if !strings.Contains(nestedConstraintStr, "(or ") {
		t.Errorf("nested union constraint should contain 'or': %v", nestedConstraintStr)
	}
	if !strings.Contains(nestedConstraintStr, "(is-OString w)") {
		t.Errorf("missing string constraint in nested union: %v", nestedConstraintStr)
	}
	if !strings.Contains(nestedConstraintStr, "(is-ONumber w)") {
		t.Errorf("missing int constraint in nested union: %v", nestedConstraintStr)
	}
	if !strings.Contains(nestedConstraintStr, "(is-OBoolean w)") {
		t.Errorf("missing boolean constraint in nested union: %v", nestedConstraintStr)
	}
}

func TestTypeDefs_getSmtConstr_UnionWithError(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}

	// Test union with unsupported member type
	badUnionType := &types.RegoTypeDef{
		Kind: types.KindUnion,
		Union: []types.RegoTypeDef{
			{Kind: types.KindAtomic, AtomicType: types.AtomicString},
			{Kind: types.KindUnknown}, // This should cause an error
		},
	}
	_, err := td.getSmtConstr("x", badUnionType)
	if err == nil {
		t.Error("expected error for union with unsupported member type, got nil")
	}

	// Test non-union type passed to getSmtUnionConstr
	nonUnionType := &types.RegoTypeDef{Kind: types.KindAtomic, AtomicType: types.AtomicString}
	_, err = td.getSmtUnionConstr("y", nonUnionType)
	if err == nil {
		t.Error("expected error for non-union type passed to getSmtUnionConstr, got nil")
	}
}

func TestGetSmtObjStoreExpr_SimpleObject(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{TypeInfo: nil}

	tp := types.NewObjectType(map[string]types.RegoTypeDef{
		"a": types.NewAtomicType(types.AtomicString),
		"b": types.NewAtomicType(types.AtomicInt),
	})

	expr, bucket, err := td.getSmtObjStoreExpr(&tp)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if bucket == nil {
		t.Fatalf("expected bucket")
	}
	if !strings.Contains(expr, "(OObj1") {
		t.Fatalf("expected object constructor in expr, got: %s", expr)
	}
	if !strings.Contains(expr, "(as const (Array String OTypeD0))") {
		t.Fatalf("expected as-const array in expr, got: %s", expr)
	}
	if !strings.Contains(expr, "(store") {
		t.Fatalf("expected store chain in expr, got: %s", expr)
	}

	decls := strings.Join(cmdStrings(bucket.Decls), "\n")
	if !strings.Contains(decls, "(declare-fun") {
		t.Fatalf("expected leaf declarations, got: %s", decls)
	}
	// Leaves are constrained via additional (assert ...) lines.
	asserts := strings.Join(cmdStrings(bucket.Asserts), "\n")
	if !strings.Contains(asserts, "(assert (is-") {
		t.Fatalf("expected atomic leaf assertions, got: %s", asserts)
	}
}

func TestGetSmtObjStoreExpr_NestedObject(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{TypeInfo: nil}

	inner := types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
		"a": types.NewAtomicType(types.AtomicString),
	}, false)}

	tp := types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
		"outer": inner,
		"flag":  types.NewAtomicType(types.AtomicBoolean),
	}, false)}

	expr, bucket, err := td.getSmtObjStoreExpr(&tp)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if bucket == nil {
		t.Fatalf("expected bucket")
	}
	if !strings.Contains(expr, "(OObj2") {
		t.Fatalf("expected top-level OObj2 constructor in expr, got: %s", expr)
	}
	if !strings.Contains(expr, "(OObj1") {
		t.Fatalf("expected nested OObj1 constructor in expr, got: %s", expr)
	}
	if !strings.Contains(expr, "(as const (Array String OTypeD1))") {
		t.Fatalf("expected as-const array of OTypeD1 in expr, got: %s", expr)
	}
	// Atomic leaves at element-depth 1 must be lifted via Atom1.
	if !strings.Contains(expr, "(Atom1") {
		t.Fatalf("expected atomic lift via Atom1 in expr, got: %s", expr)
	}
}

func TestGetSmtObjStoreExpr_RejectsAllowAdditional(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{TypeInfo: nil}

	// NewObjectType defaults to AllowAdditional=true; exported wrapper should reject.
	tpBad := types.NewObjectType(map[string]types.RegoTypeDef{
		"a": types.NewAtomicType(types.AtomicString),
	})
	_, _, err := td.GetSmtObjStoreExpr(&tpBad)
	if err == nil {
		t.Fatalf("expected error for AllowAdditional=true")
	}

	// Explicitly disallow additional properties; wrapper should accept.
	tpGood := types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
		"a": types.NewAtomicType(types.AtomicString),
		"b": types.NewAtomicType(types.AtomicInt),
	}, false)}
	_, _, err = td.GetSmtObjStoreExpr(&tpGood)
	if err != nil {
		t.Fatalf("unexpected error for AllowAdditional=false: %v", err)
	}
}

func TestGetSmtObjectConstrStore_AssertsEquality(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{TypeInfo: nil}

	tp := types.NewObjectType(map[string]types.RegoTypeDef{
		"x": types.NewAtomicType(types.AtomicBoolean),
	})

	bucket, err := td.GetSmtObjectConstrStore("obj", &tp)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if bucket == nil {
		t.Fatalf("expected bucket")
	}
	foundEq := false
	for _, a := range bucket.Asserts {
		if strings.Contains(a.String(), "(assert (= obj") {
			foundEq = true
			break
		}
	}
	if !foundEq {
		t.Fatalf("expected equality assertion against obj, got asserts: %v", bucket.Asserts)
	}
}
