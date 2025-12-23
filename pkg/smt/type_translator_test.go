package smt

import (
	"strings"
	"testing"

	"github.com/vhavlena/verirego/pkg/types"
)

func TestTypeDefs_getSmtConstr_AtomicString(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	typeDef := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicString,
	}
	constr, err := td.getSmtConstr("x", typeDef)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(constr) != 1 || constr[0] != "(is-OString x)" {
		t.Errorf("unexpected constraint: %v", constr)
	}
}

func TestTypeDefs_getSmtConstr_AtomicInt(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}
	typeDef := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicInt,
	}
	constr, err := td.getSmtConstr("y", typeDef)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(constr) != 1 || constr[0] != "(is-ONumber y)" {
		t.Errorf("unexpected constraint: %v", constr)
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
	constr, err := td.getSmtConstr("z", objType)
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
	for _, c := range constr {
		if _, ok := want[c]; ok {
			want[c] = true
		}
		if _, ok := atomicChecks[c]; ok {
			atomicChecks[c] = true
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
	constr, err := td.getSmtConstr("n", nestedType)
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
	for _, c := range constr {
		if _, ok := want[c]; ok {
			want[c] = true
		}
		if _, ok := atomicChecks[c]; ok {
			atomicChecks[c] = true
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
	assertStr, err := td.getSmtConstrAssert("n", nestedType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
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
	constr, err := td.getSmtArrConstr("a", arrType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(constr) != 2 {
		t.Errorf("expected 2 constraints, got %d", len(constr))
	}
	if constr[0] != "(is-OArray1 a)" {
		t.Errorf("missing or incorrect OArray constraint: %v", constr[0])
	}
	if !strings.Contains(constr[1], "(is-OString elem)") {
		t.Errorf("missing or incorrect atomic string constraint in forall: %v", constr[1])
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
	nestedConstr, err := td.getSmtArrConstr("b", nestedArrType)

	if err != nil {
		t.Fatalf("unexpected error for nested array: %v", err)
	}
	if len(nestedConstr) != 2 {
		t.Errorf("expected 2 constraints for nested array, got %d", len(nestedConstr))
	}
	if nestedConstr[0] != "(is-OArray2 b)" {
		t.Errorf("missing or incorrect OArray constraint for nested array: %v", nestedConstr[0])
	}
	if !strings.Contains(nestedConstr[1], "(is-OArray1 elem)") {
		t.Errorf("missing or incorrect nested OArray constraint in forall: %v", nestedConstr[1])
	}
	if !strings.Contains(nestedConstr[1], "(is-ONumber elem") {
		t.Errorf("missing or incorrect atomic int constraint in nested forall: %v", nestedConstr[1])
	}
}

func TestTypeDefs_getSmtConstr_Union(t *testing.T) {
	t.Parallel()
	td := &TypeTranslator{}

	// Test simple union: string | int
	simpleUnionType := &types.RegoTypeDef{
		Kind: types.KindUnion,
		Union: []types.RegoTypeDef{
			{
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicString,
			},
			{
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicInt,
			},
		},
	}
	constr, err := td.getSmtConstr("u", simpleUnionType)
	if err != nil {
		t.Fatalf("unexpected error for simple union: %v", err)
	}
	if len(constr) != 1 {
		t.Errorf("expected 1 constraint for simple union, got %d", len(constr))
	}
	if !strings.Contains(constr[0], "(or ") {
		t.Errorf("union constraint should contain 'or': %v", constr[0])
	}
	if !strings.Contains(constr[0], "(is-OString u)") {
		t.Errorf("missing string constraint in union: %v", constr[0])
	}
	if !strings.Contains(constr[0], "(is-ONumber u)") {
		t.Errorf("missing int constraint in union: %v", constr[0])
	}

	// Test complex union: string | object | array
	complexUnionType := &types.RegoTypeDef{
		Kind: types.KindUnion,
		Union: []types.RegoTypeDef{
			{
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicString,
			},
			{
				Kind: types.KindObject,
				ObjectFields: types.NewObjectFieldSet(map[string]types.RegoTypeDef{
					"field1": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicBoolean,
					},
				}, false),
			},
			{
				Kind: types.KindArray,
				ArrayType: &types.RegoTypeDef{
					Kind:       types.KindAtomic,
					AtomicType: types.AtomicInt,
				},
			},
		},
	}
	complexConstr, err := td.getSmtConstr("v", complexUnionType)
	if err != nil {
		t.Fatalf("unexpected error for complex union: %v", err)
	}
	if len(complexConstr) != 1 {
		t.Errorf("expected 1 constraint for complex union, got %d", len(complexConstr))
	}
	complexConstraintStr := complexConstr[0]
	if !strings.Contains(complexConstraintStr, "(or ") {
		t.Errorf("complex union constraint should contain 'or': %v", complexConstraintStr)
	}
	// Check that it contains all member constraints
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
					{
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicString,
					},
					{
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicInt,
					},
				},
			},
			{
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicBoolean,
			},
		},
	}
	nestedConstr, err := td.getSmtConstr("w", nestedUnionType)
	if err != nil {
		t.Fatalf("unexpected error for nested union: %v", err)
	}
	if len(nestedConstr) != 1 {
		t.Errorf("expected 1 constraint for nested union, got %d", len(nestedConstr))
	}
	nestedConstraintStr := nestedConstr[0]
	if !strings.Contains(nestedConstraintStr, "(or ") {
		t.Errorf("nested union constraint should contain 'or': %v", nestedConstraintStr)
	}
	// Should contain all flattened constraints
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
			{
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicString,
			},
			{
				Kind: types.KindUnknown, // This should cause an error
			},
		},
	}
	_, err := td.getSmtConstr("x", badUnionType)
	if err == nil {
		t.Error("expected error for union with unsupported member type, got nil")
	}

	// Test non-union type passed to getSmtUnionConstr
	nonUnionType := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicString,
	}
	_, err = td.getSmtUnionConstr("y", nonUnionType)
	if err == nil {
		t.Error("expected error for non-union type passed to getSmtUnionConstr, got nil")
	}
}
