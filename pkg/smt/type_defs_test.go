package smt

import (
	"strings"
	"testing"

	"github.com/vhavlena/verirego/pkg/types"
)

func TestTranslator_getSmtConstr_AtomicString(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	typeDef := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicString,
	}
	constr, err := tr.getSmtConstr("x", typeDef)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(constr) != 1 || constr[0] != "(is-OString (atom x))" {
		t.Errorf("unexpected constraint: %v", constr)
	}
}

func TestTranslator_getSmtConstr_AtomicInt(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	typeDef := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: types.AtomicInt,
	}
	constr, err := tr.getSmtConstr("y", typeDef)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(constr) != 1 || constr[0] != "(is-ONumber (atom y))" {
		t.Errorf("unexpected constraint: %v", constr)
	}
}

func TestTranslator_getSmtConstr_Object(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	objType := &types.RegoTypeDef{
		Kind: types.KindObject,
		ObjectFields: map[string]types.RegoTypeDef{
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
				ObjectFields: map[string]types.RegoTypeDef{
					"x": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicBoolean,
					},
				},
			},
		},
	}
	constr, err := tr.getSmtConstr("z", objType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := map[string]bool{
		"(is-OObj (select (obj z) \"baz\"))": false,
	}
	atomicChecks := map[string]bool{
		"(is-OString (atom (select (obj z) \"foo\")))":                       false,
		"(is-ONumber (atom (select (obj z) \"bar\")))":                       false,
		"(is-OBoolean (atom (select (obj (select (obj z) \"baz\")) \"x\")))": false,
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

func TestTranslator_getSmtConstr_NestedObject(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	nestedType := &types.RegoTypeDef{
		Kind: types.KindObject,
		ObjectFields: map[string]types.RegoTypeDef{
			"outer": {
				Kind: types.KindObject,
				ObjectFields: map[string]types.RegoTypeDef{
					"inner": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicString,
					},
					"num": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicInt,
					},
				},
			},
			"flag": {
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicBoolean,
			},
		},
	}
	constr, err := tr.getSmtConstr("n", nestedType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := map[string]bool{
		"(is-OObj (select (obj n) \"outer\"))": false,
	}
	atomicChecks := map[string]bool{
		"(is-OBoolean (atom (select (obj n) \"flag\")))":                          false,
		"(is-OString (atom (select (obj (select (obj n) \"outer\")) \"inner\")))": false,
		"(is-ONumber (atom (select (obj (select (obj n) \"outer\")) \"num\")))":   false,
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

func TestTranslator_getSmtConstr_UnsupportedType(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	unknownType := &types.RegoTypeDef{Kind: types.KindUnknown}
	_, err := tr.getSmtConstr("v", unknownType)
	if err == nil {
		t.Error("expected error for unsupported type, got nil")
	}
}

func TestTranslator_getSmtConstr_UnsupportedAtomic(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	badAtomic := &types.RegoTypeDef{
		Kind:       types.KindAtomic,
		AtomicType: "invalid-atomic-type", // invalid atomic type
	}
	_, err := tr.getSmtConstr("w", badAtomic)
	if err == nil {
		t.Error("expected error for unsupported atomic type, got nil")
	}
}

func TestTranslator_getSmtConstrAssert_NestedObject(t *testing.T) {
	t.Parallel()
	tr := &Translator{}
	nestedType := &types.RegoTypeDef{
		Kind: types.KindObject,
		ObjectFields: map[string]types.RegoTypeDef{
			"outer": {
				Kind: types.KindObject,
				ObjectFields: map[string]types.RegoTypeDef{
					"inner": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicString,
					},
					"num": {
						Kind:       types.KindAtomic,
						AtomicType: types.AtomicInt,
					},
				},
			},
			"flag": {
				Kind:       types.KindAtomic,
				AtomicType: types.AtomicBoolean,
			},
		},
	}
	assertStr, err := tr.getSmtConstrAssert("n", nestedType)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	checks := []string{
		"(is-OObj (select (obj n) \"outer\"))",
		"(is-OBoolean (atom (select (obj n) \"flag\")))",
		"(is-OString (atom (select (obj (select (obj n) \"outer\")) \"inner\")))",
		"(is-ONumber (atom (select (obj (select (obj n) \"outer\")) \"num\")))",
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
