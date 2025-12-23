package smt

import (
	"fmt"
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
	z3 "github.com/vhavlena/z3-go/z3"
)

// helper to run an SMT-LIB2 string with z3 and expect SAT
func expectSatZ3(t *testing.T, smt string) {
	t.Helper()
	ctx := z3.NewContext(nil)
	defer ctx.Close()
	solver := ctx.NewSolver()
	defer solver.Close()
	if err := solver.AssertSMTLIB2String(smt); err != nil {
		t.Fatalf("z3 AssertSMTLIB2String error: %v\nSMT:\n%s", err, smt)
	}
	res, err := solver.Check()
	if err != nil {
		t.Fatalf("z3 Check error: %v", err)
	}
	if res != z3.Sat {
		t.Fatalf("expected SAT, got %v\nSMT:\n%s", res, smt)
	}
}

func buildTypeTranslator(t *testing.T, tm map[string]types.RegoTypeDef) *TypeTranslator {
	t.Helper()
	return NewTypeDefs(&types.TypeAnalyzer{Types: tm, Refs: map[string]ast.Value{}})
}

func Test_getSmtConstrAssert_Object(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name string
		obj  types.RegoTypeDef
	}{
		// {
		// 	name: "NoAdditional",
		// 	// x: object{ a: string }, AllowAdditional=false
		// 	obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
		// 		"a": types.NewAtomicType(types.AtomicString),
		// 	}, AllowAdditional: false}},
		// },
		{
			name: "AdditionalString",
			// x: object{ a: int, *: string }, AllowAdditional=true
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"a":                     types.NewAtomicType(types.AtomicInt),
				types.AdditionalPropKey: types.NewAtomicType(types.AtomicString),
			}, AllowAdditional: true}},
		},
		{
			name: "AdditionalAbsent",
			// x: object{ a: boolean }, AllowAdditional=true but no AdditionalPropKey
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"a": types.NewAtomicType(types.AtomicBoolean),
			}, AllowAdditional: true}},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			tr := buildTypeTranslator(t, map[string]types.RegoTypeDef{"x": tt.obj})
			used := map[string]any{"x": struct{}{}}
			bucket, err := tr.GenerateTypeDecls(used)
			if err != nil {
				t.Fatalf("type decls error: %v", err)
			}

			decl, err := tr.getVarDeclaration("x", &tt.obj)
			if err != nil {
				t.Fatalf("decl error: %v", err)
			}
			constr, err := tr.getSmtConstrAssert("x", &tt.obj)
			if err != nil {
				t.Fatalf("constr error: %v", err)
			}

			smt := strings.Join(append(append([]string{}, bucket.TypeDecls...), decl, constr), "\n")
			fmt.Printf("%s\n", smt)
			expectSatZ3(t, smt)
		})
	}
}
