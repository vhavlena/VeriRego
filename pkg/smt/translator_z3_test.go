package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
	z3 "github.com/vhavlena/z3-go/z3"
)

// TestTranslateAndCheckZ3 translates a tiny Rego module to SMT-LIB and checks SAT with Z3.
//
// Build/run with Z3 available:
//
//	go test -tags z3 ./...
func TestTranslateAndCheckZ3(t *testing.T) {
	// Simple, satisfiable module: p = x with body x == 1
	rego := `
	package test

	p(a) := x if {
		x == 1
	}
`

	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}

	// Minimal type info for variables used in the rule
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
			"p": types.NewAtomicType(types.AtomicInt),
		},
		Refs: map[string]ast.Value{
			"x": ast.Var("x"),
			"p": ast.Var("p"),
		},
	}

	tr := NewTranslator(ta, mod)

	// Declare only the variables we actually use (avoid schema auto-includes)
	used := map[string]any{"x": struct{}{}, "p": struct{}{}}

	// Generate type and var declarations
	if bucket, err := tr.TypeTrans.GenerateTypeDecls(used); err != nil {
		t.Fatalf("type decls error: %v", err)
	} else {
		tr.AppendBucket(bucket)
	}
	if bucket, err := tr.TypeTrans.GenerateVarDecls(used); err != nil {
		t.Fatalf("var decls error: %v", err)
	} else {
		tr.AppendBucket(bucket)
	}

	// Translate rules to asserts
	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}

	smt := strings.Join(tr.SmtLines(), "\n")
	println("--- smt ---", smt)

	// Z3: assert SMT-LIB2 string and check SAT
	ctx := z3.NewContext(nil)
	defer ctx.Close()
	solver := ctx.NewSolver()
	defer solver.Close()

	if err := solver.AssertSMTLIB2String(smt); err != nil {
		t.Fatalf("z3 AssertSMTLIB2String error: %v", err)
	}
	res, err := solver.Check()
	if err != nil {
		t.Fatalf("z3 Check error: %v", err)
	}

	// Expect the formula to be satisfiable
	if res != z3.Sat {
		t.Fatalf("expected SAT, got %v", res)
	}
}
