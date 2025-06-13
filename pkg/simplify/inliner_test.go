package simplify

import (
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

func TestInlineRuleBody(t *testing.T) {
	re := `package test

foo(x) {
  x > 1
}

bar(y) {
  foo(y)
  y < 10
}`
	module, err := ast.ParseModule("test.rego", re)
	if err != nil {
		t.Fatalf("failed to parse module: %v", err)
	}
	inliner := NewInliner()
	inliner.GatherInlinePredicates(module)

	// Find the bar rule
	var barRule *ast.Rule
	for _, rule := range module.Rules {
		if rule.Head.Name.String() == "bar" {
			barRule = rule
			break
		}
	}
	if barRule == nil {
		t.Fatal("bar rule not found")
	}

	inlinedBody := inliner.InlineRuleBody(barRule)
	if len(inlinedBody) != 2 {
		t.Errorf("expected 2 expressions after inlining, got %d", len(inlinedBody))
	}
	// The first should be 'y > 1', the second 'y < 10'
	exprStrs := []string{inlinedBody[0].String(), inlinedBody[1].String()}
	if exprStrs[0] != ast.GreaterThan.Expr(ast.VarTerm("y"), ast.IntNumberTerm(1)).String() {
		t.Errorf("expected first expr to be 'y > 1', got %v", exprStrs[0])
	}
	if exprStrs[1] != ast.LessThan.Expr(ast.VarTerm("y"), ast.IntNumberTerm(10)).String() {
		t.Errorf("expected second expr to be 'y < 10', got %v", exprStrs[1])
	}
}
