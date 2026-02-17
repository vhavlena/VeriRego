package smt

import (
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
	z3 "github.com/vhavlena/z3-go/z3"
)

func runningInGitHubActions() bool {
	return os.Getenv("GITHUB_ACTIONS") == "true"
}

func cmdStringsZ3(cmds []*SmtCommand) []string {
	out := make([]string, 0, len(cmds))
	for _, c := range cmds {
		out = append(out, c.String())
	}
	return out
}

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
		{
			name: "NoAdditional",
			// x: object{ a: string }, AllowAdditional=false
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"a": types.NewAtomicType(types.AtomicString),
			}, AllowAdditional: false}},
		},
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
			if runningInGitHubActions() && tt.name == "NoAdditional" {
				t.Skip("skipping NoAdditional object test on GitHub Actions (too heavy/flaky in CI)")
			}
			t.Parallel()
			tr := buildTypeTranslator(t, map[string]types.RegoTypeDef{"x": tt.obj})
			used := map[string]any{"x": struct{}{}}
			bucket, err := tr.GenerateTypeDecls(used)
			if err != nil {
				t.Fatalf("type decls error: %v", err)
			}

			declBucket, err := tr.getVarDeclaration("x", &tt.obj)
			if err != nil {
				t.Fatalf("decl error: %v", err)
			}
			constrBucket, err := tr.getSmtConstrAssert("x", &tt.obj)
			if err != nil {
				t.Fatalf("constr error: %v", err)
			}

			smtLines := make([]string, 0, len(bucket.TypeDecls)+len(declBucket.Decls)+len(constrBucket.Asserts)+2)
			smtLines = append(smtLines, cmdStringsZ3(bucket.TypeDecls)...)
			smtLines = append(smtLines, cmdStringsZ3(declBucket.Decls)...)
			smtLines = append(smtLines, cmdStringsZ3(constrBucket.Asserts)...)
			smt := strings.Join(smtLines, "\n")
			fmt.Printf("%s\n", smt)
			expectSatZ3(t, smt)
		})
	}
}

func Test_getSmtObjectConstrStore_SimpleObject_Z3(t *testing.T) {
	t.Parallel()

	obj := types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
		"a": types.NewAtomicType(types.AtomicString),
		"b": types.NewAtomicType(types.AtomicInt),
		"c": types.NewAtomicType(types.AtomicBoolean),
	}, AllowAdditional: false}}

	tr := buildTypeTranslator(t, map[string]types.RegoTypeDef{"x": obj})
	used := map[string]any{"x": struct{}{}}

	typeBucket, err := tr.GenerateTypeDecls(used)
	if err != nil {
		t.Fatalf("type decls error: %v", err)
	}
	declBucket, err := tr.getVarDeclaration("x", &obj)
	if err != nil {
		t.Fatalf("decl error: %v", err)
	}
	storeBucket, err := tr.GetSmtObjectConstrStore("x", &obj)
	if err != nil {
		t.Fatalf("store constr error: %v", err)
	}

	smtLines := make([]string, 0, len(typeBucket.TypeDecls)+len(declBucket.Decls)+len(storeBucket.Decls)+len(storeBucket.Asserts)+2)
	smtLines = append(smtLines, cmdStringsZ3(typeBucket.TypeDecls)...)
	smtLines = append(smtLines, cmdStringsZ3(declBucket.Decls)...)
	smtLines = append(smtLines, cmdStringsZ3(storeBucket.Decls)...)
	smtLines = append(smtLines, cmdStringsZ3(storeBucket.Asserts)...)
	smt := strings.Join(smtLines, "\n")

	if !strings.Contains(smt, "(as const (Array String") {
		t.Fatalf("expected as const in SMT, got:\n%s", smt)
	}
	if !strings.Contains(smt, "(store") {
		t.Fatalf("expected store in SMT, got:\n%s", smt)
	}

	expectSatZ3(t, smt)
}

func Test_getSmtObjectConstrStore_VariousObjects_Z3(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name          string
		obj           types.RegoTypeDef
		expectStore   bool
		expectHas     []string
		skipInActions bool
	}{
		{
			name: "SimpleABC_NoAdditional",
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"a": types.NewAtomicType(types.AtomicString),
				"b": types.NewAtomicType(types.AtomicInt),
				"c": types.NewAtomicType(types.AtomicBoolean),
			}, AllowAdditional: false}},
			expectStore: true,
		},
		{
			name: "NestedDepth2_NoAdditional",
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"outer": {Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
					"a": types.NewAtomicType(types.AtomicString),
					"b": types.NewAtomicType(types.AtomicInt),
				}, AllowAdditional: false}},
				"flag": types.NewAtomicType(types.AtomicBoolean),
			}, AllowAdditional: false}},
			expectStore: true,
			expectHas:   []string{"(OObj2", "(OObj1", "(Atom1"},
		},
		{
			name: "NestedDepth3_NoAdditional",
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"outer": {Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
					"inner": {Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
						"a": types.NewAtomicType(types.AtomicString),
					}, AllowAdditional: false}},
					"n": types.NewAtomicType(types.AtomicInt),
				}, AllowAdditional: false}},
				"outer2": {Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
					"a": types.NewAtomicType(types.AtomicString),
					"b": types.NewAtomicType(types.AtomicInt),
				}, AllowAdditional: false}},
			}, AllowAdditional: false}},
			expectStore: true,
			expectHas:   []string{"(OObj3", "(OObj2", "(OObj1", "(Atom2", "(Atom1"},
		},
		{
			name:        "EmptyObject_NoAdditional",
			obj:         types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{}, AllowAdditional: false}},
			expectStore: false,
		},
		{
			name: "AllowAdditional_WithoutStar",
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"a": types.NewAtomicType(types.AtomicBoolean),
			}, AllowAdditional: true}},
			expectStore: true,
		},
		{
			name: "AllowAdditional_WithStarAtomic",
			obj: types.RegoTypeDef{Kind: types.KindObject, ObjectFields: types.ObjectFieldSet{Fields: map[string]types.RegoTypeDef{
				"a":                     types.NewAtomicType(types.AtomicInt),
				types.AdditionalPropKey: types.NewAtomicType(types.AtomicString),
			}, AllowAdditional: true}},
			expectStore: true,
		},
	}

	for _, tt := range tests {
		tt := tt
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()

			tr := buildTypeTranslator(t, map[string]types.RegoTypeDef{"x": tt.obj})
			used := map[string]any{"x": struct{}{}}

			typeBucket, err := tr.GenerateTypeDecls(used)
			if err != nil {
				t.Fatalf("type decls error: %v", err)
			}
			declBucket, err := tr.getVarDeclaration("x", &tt.obj)
			if err != nil {
				t.Fatalf("decl error: %v", err)
			}
			storeBucket, err := tr.GetSmtObjectConstrStore("x", &tt.obj)
			if err != nil {
				t.Fatalf("store constr error: %v", err)
			}

			smtLines := make([]string, 0, len(typeBucket.TypeDecls)+len(declBucket.Decls)+len(storeBucket.Decls)+len(storeBucket.Asserts)+2)
			smtLines = append(smtLines, cmdStringsZ3(typeBucket.TypeDecls)...)
			smtLines = append(smtLines, cmdStringsZ3(declBucket.Decls)...)
			smtLines = append(smtLines, cmdStringsZ3(storeBucket.Decls)...)
			smtLines = append(smtLines, cmdStringsZ3(storeBucket.Asserts)...)
			smt := strings.Join(smtLines, "\n")

			if !strings.Contains(smt, "(as const (Array String") {
				t.Fatalf("expected as const in SMT, got:\n%s", smt)
			}
			if tt.expectStore {
				if !strings.Contains(smt, "(store") {
					t.Fatalf("expected store in SMT, got:\n%s", smt)
				}
			} else {
				if strings.Contains(smt, "(store") {
					t.Fatalf("did not expect store in SMT, got:\n%s", smt)
				}
			}
			if !strings.Contains(smt, "(assert (= x ") {
				t.Fatalf("expected equality assertion against x, got:\n%s", smt)
			}
			for _, sub := range tt.expectHas {
				if !strings.Contains(smt, sub) {
					t.Fatalf("expected SMT to contain %q, got:\n%s", sub, smt)
				}
			}

			expectSatZ3(t, smt)
		})
	}
}
