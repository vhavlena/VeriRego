package simplify

import (
	"fmt"
	"testing"

	"github.com/open-policy-agent/opa/ast"
)

func TestSubstituteVars(t *testing.T) {
	t.Parallel()
	// xVar := ast.Var("x")
	one := ast.IntNumberTerm(1)
	expr := ast.Equality.Expr(ast.VarTerm("x"), one)

	// Substitute x -> 2
	two := ast.IntNumberTerm(2)
	argMap := map[string]*ast.Term{"x": two}
	newExpr := substituteVars(expr, argMap)

	terms, ok := newExpr.Terms.([]*ast.Term)
	if !ok || len(terms) != 3 {
		t.Fatalf("unexpected terms: %v", newExpr.Terms)
	}
	if terms[1].Value.Compare(two.Value) != 0 {
		t.Errorf("expected second term to be 2, got %v", terms[1].Value)
	}
}

func TestSubstituteTerms(t *testing.T) {
	t.Parallel()
	// xVar := ast.Var("x")
	// yVar := ast.Var("y")
	xTerm := ast.VarTerm("x")
	yTerm := ast.VarTerm("y")
	three := ast.IntNumberTerm(3)
	four := ast.IntNumberTerm(4)
	argMap := map[string]*ast.Term{"x": three, "y": four}

	// Single term substitution
	res := substituteTerms(xTerm, argMap)
	if term, ok := res.(*ast.Term); !ok || term.Value.Compare(three.Value) != 0 {
		t.Errorf("expected term to be 3, got %v", res)
	}

	// Slice of terms substitution
	terms := []*ast.Term{xTerm, yTerm}
	res2 := substituteTerms(terms, argMap)
	newTerms, ok := res2.([]*ast.Term)
	if !ok || len(newTerms) != 2 {
		t.Fatalf("unexpected result: %v", res2)
	}
	if newTerms[0].Value.Compare(three.Value) != 0 || newTerms[1].Value.Compare(four.Value) != 0 {
		t.Errorf("expected terms to be 3 and 4, got %v and %v", newTerms[0].Value, newTerms[1].Value)
	}
}

func TestInlineExpr(t *testing.T) {
	t.Parallel()
	// Case 1: Not a function call (should return original expr)
	expr := ast.Equality.Expr(ast.VarTerm("x"), ast.IntNumberTerm(1))
	funcDefs := map[string]*ast.Rule{}
	result := inlineExpr(expr, funcDefs)
	if len(result) != 1 || result[0] != expr {
		t.Errorf("expected original expr, got %v", result)
	}

	// Case 2: Function call, but not in funcDefs (should return original expr)
	callExpr := &ast.Expr{
		Terms: []*ast.Term{
			ast.VarTerm("foo"), ast.IntNumberTerm(2),
		},
	}
	result = inlineExpr(callExpr, funcDefs)
	if len(result) != 1 || result[0] != callExpr {
		t.Errorf("expected original callExpr, got %v", result)
	}

	// Case 3: Function call, function in funcDefs (should inline body only)
	// foo(x) = y { y := x + 1 }
	fooRule, err := ast.ParseRule(`foo(x) = y { y := x + 1 }`)
	if err != nil {
		t.Fatalf("failed to parse rule: %v", err)
	}
	funcDefs["foo"] = fooRule
	callExpr = &ast.Expr{
		Terms: []*ast.Term{
			ast.VarTerm("foo"), ast.IntNumberTerm(5),
		},
	}
	result = inlineExpr(callExpr, funcDefs)
	if len(result) == 0 {
		t.Fatalf("expected inlined body, got empty result")
	}
	// Check that the inlined body is 'y := 5 + 1'
	plusCall := &ast.Call{
		ast.VarTerm("plus"), ast.IntNumberTerm(5), ast.IntNumberTerm(1),
	}
	plusTerm := ast.NewTerm(plusCall)
	expected := ast.Assign.Expr(ast.VarTerm("y"), plusTerm)
	found := false
	for _, e := range result {
		fmt.Printf("Debug: Inlined expr: %v %v\n", e, expected)

		if e.String() == expected.String() {
			found = true
		}
	}
	if !found {
		t.Errorf("expected inlined expr to contain 'y := 5 + 1', got %v", result)
	}
}

func TestGatherInlinePredicates(t *testing.T) {
	t.Parallel()
	rego := `package test

allow {
	input.user == "admin"
}

is_valid {
	true
}

single_true {
	input.x > 0
}

multi_body {
	input.x > 0
	input.y < 5
}

not_true {
	input.x == 1
}

inline_true {
	true
}`
	module, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse module: %v", err)
	}

	inliner := NewInliner()
	inliner.GatherInlinePredicates(module)
	inlinePreds := inliner.inlinePreds

	if len(inlinePreds) != 5 {
		t.Errorf("expected 5 inline predicates, got %d", len(inlinePreds))
	}
	if _, ok := inlinePreds["is_valid"]; !ok {
		t.Errorf("expected 'is_valid' to be an inline predicate")
	}
	if _, ok := inlinePreds["inline_true"]; !ok {
		t.Errorf("expected 'inline_true' to be an inline predicate")
	}
	if _, ok := inlinePreds["allow"]; !ok {
		t.Errorf("did not expect 'allow' to be an inline predicate")
	}
	if _, ok := inlinePreds["multi_body"]; ok {
		t.Errorf("did not expect 'multi_body' to be an inline predicate")
	}
}
