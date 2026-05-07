package types

import (
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
)

// countOperator walks all rule expressions and counts how many have the given operator name.
func countOperator(mod *ast.Module, op string) int {
	n := 0
	for _, rule := range mod.Rules {
		ast.WalkExprs(rule, func(e *ast.Expr) bool {
			terms, ok := e.Terms.([]*ast.Term)
			if ok && len(terms) > 0 && terms[0].String() == op {
				n++
			}
			return false
		})
	}
	return n
}

// TestRestoreEqualityOperators_OnlyEq rewrites compiled eq back to equal for ==.
func TestRestoreEqualityOperators_OnlyEq(t *testing.T) {
	src := `package test
check if { x := 1; x == 2 }`
	mod, err := ast.ParseModule("test.rego", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	compiled := compileModule(t, mod)

	if n := countOperator(compiled, "equal"); n != 0 {
		t.Fatalf("expected 0 'equal' nodes before restore, got %d", n)
	}

	restored := RestoreEqualityOperators(mod, compiled)

	if n := countOperator(restored, "equal"); n != 1 {
		t.Errorf("expected 1 'equal' node after restore, got %d", n)
	}
	if n := countOperator(restored, "eq"); n == 0 {
		t.Errorf("expected at least one 'eq' node for assignment to remain")
	}
}

// TestRestoreEqualityOperators_NoEq is a no-op when the module has no ==.
func TestRestoreEqualityOperators_NoEq(t *testing.T) {
	src := `package test
check if { x := 1; x > 0 }`
	mod, err := ast.ParseModule("test.rego", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	compiled := compileModule(t, mod)
	before := countOperator(compiled, "eq")

	restored := RestoreEqualityOperators(mod, compiled)

	if n := countOperator(restored, "equal"); n != 0 {
		t.Errorf("expected 0 'equal' nodes, got %d", n)
	}
	if countOperator(restored, "eq") != before {
		t.Errorf("eq count changed unexpectedly")
	}
}

// TestRestoreEqualityOperators_MixedOps distinguishes == from = on the same rule.
func TestRestoreEqualityOperators_MixedOps(t *testing.T) {
	src := `package test
check if { x := 1; y := "hello"; x == 1 }`
	mod, err := ast.ParseModule("test.rego", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	compiled := compileModule(t, mod)
	restored := RestoreEqualityOperators(mod, compiled)

	if n := countOperator(restored, "equal"); n != 1 {
		t.Errorf("expected exactly 1 'equal' node, got %d", n)
	}
	if n := countOperator(restored, "eq"); n < 2 {
		t.Errorf("expected at least 2 'eq' nodes for assignments, got %d", n)
	}
}
