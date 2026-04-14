package simplify

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
)

// ─── helpers ─────────────────────────────────────────────────────────────────

func mustParseModule(t *testing.T, src string) *ast.Module {
	t.Helper()
	m, err := ast.ParseModuleWithOpts("test.rego", src, ast.ParserOptions{})
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	return m
}

// collectAllVarNames returns a map from variable name to occurrence count,
// scanning the rule's head, body, and else branches.
func collectAllVarNames(rule *ast.Rule) map[string]int {
	counts := make(map[string]int)
	var scanTerm func(*ast.Term)
	scanTerm = func(t *ast.Term) {
		if t == nil {
			return
		}
		switch v := t.Value.(type) {
		case ast.Var:
			counts[string(v)]++
		case ast.Ref:
			for _, seg := range v {
				scanTerm(seg)
			}
		case *ast.Array:
			for i := range v.Len() {
				scanTerm(v.Elem(i))
			}
		case ast.Object:
			v.Foreach(func(k, val *ast.Term) { scanTerm(k); scanTerm(val) })
		case ast.Set:
			v.Foreach(scanTerm)
		case ast.Call:
			for _, ct := range v {
				scanTerm(ct)
			}
		}
	}
	var scanExpr func(*ast.Expr)
	scanExpr = func(expr *ast.Expr) {
		switch terms := expr.Terms.(type) {
		case *ast.Term:
			scanTerm(terms)
		case []*ast.Term:
			for _, t := range terms {
				scanTerm(t)
			}
		}
		for _, w := range expr.With {
			scanTerm(w.Target)
			scanTerm(w.Value)
		}
	}
	var scanRule func(*ast.Rule)
	scanRule = func(r *ast.Rule) {
		scanTerm(r.Head.Value)
		scanTerm(r.Head.Key)
		for _, arg := range r.Head.Args {
			scanTerm(arg)
		}
		for _, expr := range r.Body {
			scanExpr(expr)
		}
		if r.Else != nil {
			scanRule(r.Else)
		}
	}
	scanRule(rule)
	return counts
}

// ─── tests ────────────────────────────────────────────────────────────────────

// A local variable must be replaced with a fresh name.
func TestSimplifyRule_LocalVarRenamed(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    x := 1
    x > 0
}`
	module := mustParseModule(t, src)
	rule := module.Rules[0]

	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(rule)

	vars := collectAllVarNames(renamed)
	if vars["x"] > 0 {
		t.Errorf("original variable 'x' should have been renamed but is still present")
	}
	found := false
	for name := range vars {
		if strings.HasPrefix(name, "__lv") {
			found = true
		}
	}
	if !found {
		t.Errorf("expected a fresh __lv* variable in the renamed rule, got %v", vars)
	}
}

// All occurrences of the same local variable must map to the SAME fresh name
// so that the rule's semantics are preserved.
func TestSimplifyRule_ConsistentRenaming(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    x := 1
    x > 0
}`
	module := mustParseModule(t, src)
	rule := module.Rules[0]

	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(rule)

	// There must be exactly one distinct __lv* name used for 'x'.
	freshNames := map[string]bool{}
	vars := collectAllVarNames(renamed)
	for name := range vars {
		if strings.HasPrefix(name, "__lv") {
			freshNames[name] = true
		}
	}
	if len(freshNames) != 1 {
		t.Errorf("expected exactly 1 fresh name for 'x', got %v", freshNames)
	}
}

// The original rule must not be mutated by SimplifyRule.
func TestSimplifyRule_OriginalUnchanged(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    y := "hello"
    y != ""
}`
	module := mustParseModule(t, src)
	rule := module.Rules[0]
	r := NewLocalVarRenamer()
	r.SimplifyRule(rule)

	vars := collectAllVarNames(rule)
	if vars["y"] == 0 {
		t.Error("original rule should still contain 'y' after SimplifyRule (copy semantics)")
	}
}

// Two rules with identically named local variables must receive distinct fresh
// names when processed by the same renamer.
func TestSimplifyModule_CrossRuleUniqueness(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    x := 1
    x > 0
}
deny if {
    x := 2
    x < 0
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	newModule := r.SimplifyModule(module)

	if len(newModule.Rules) != 2 {
		t.Fatalf("expected 2 rules, got %d", len(newModule.Rules))
	}

	vars0 := collectAllVarNames(newModule.Rules[0])
	vars1 := collectAllVarNames(newModule.Rules[1])

	if vars0["x"] > 0 || vars1["x"] > 0 {
		t.Error("original 'x' should not appear in any renamed rule")
	}

	var names0, names1 []string
	for name := range vars0 {
		if strings.HasPrefix(name, "__lv") {
			names0 = append(names0, name)
		}
	}
	for name := range vars1 {
		if strings.HasPrefix(name, "__lv") {
			names1 = append(names1, name)
		}
	}
	if len(names0) == 0 {
		t.Error("rule 0: expected at least one __lv* variable")
	}
	if len(names1) == 0 {
		t.Error("rule 1: expected at least one __lv* variable")
	}
	for _, n0 := range names0 {
		for _, n1 := range names1 {
			if n0 == n1 {
				t.Errorf("rules 0 and 1 share fresh variable name %q", n0)
			}
		}
	}
}

// Multiple distinct local variables in one rule must each get their own fresh name.
func TestSimplifyRule_MultipleLocals(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    a := 1
    b := 2
    a + b > 0
}`
	module := mustParseModule(t, src)
	rule := module.Rules[0]
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(rule)

	vars := collectAllVarNames(renamed)
	if vars["a"] > 0 || vars["b"] > 0 {
		t.Errorf("original variables 'a'/'b' should have been renamed, got %v", vars)
	}

	freshCount := 0
	for name := range vars {
		if strings.HasPrefix(name, "__lv") {
			freshCount++
		}
	}
	if freshCount < 2 {
		t.Errorf("expected at least 2 fresh variables for 'a' and 'b', got %d", freshCount)
	}
}

// SimplifyModule must not mutate the original module.
func TestSimplifyModule_OriginalUnchanged(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    z := "foo"
    z == "foo"
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	r.SimplifyModule(module)

	vars := collectAllVarNames(module.Rules[0])
	if vars["z"] == 0 {
		t.Error("original module rule should still contain 'z' after SimplifyModule")
	}
}

// Each "_" wildcard occurrence (compiled by OPA to "$0", "$1", etc.) must be
// replaced by a distinct fresh name.
func TestSimplifyRule_WildcardsReplaced(t *testing.T) {
	src := `package test
import rego.v1
foo = true if {
    __local0__ = data.test.sites[_].servers[_].hostname
    gt(__local0__, 3)
}`
	module := mustParseModule(t, src)
	rule := module.Rules[0]
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(rule)

	vars := collectAllVarNames(renamed)
	if vars["_"] > 0 {
		t.Errorf("wildcard '_' should have been replaced but is still present")
	}

	// There must be at least two distinct fresh names for the two "_" occurrences.
	freshNames := map[string]bool{}
	for name := range vars {
		if strings.HasPrefix(name, "__lv") {
			freshNames[name] = true
		}
	}
	if len(freshNames) < 2 {
		t.Errorf("expected at least 2 distinct fresh names for two '_' occurrences, got %v", freshNames)
	}
}

// A variable used as the return value (head value) must be renamed.
func TestSimplifyRule_HeadValueVarRenamed(t *testing.T) {
	src := `package test
import rego.v1
foo := x if {
    input.bar[x] == 1
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(module.Rules[0])

	s := renamed.String()
	if strings.Contains(s, "x") {
		t.Errorf("head-value variable 'x' should have been renamed, got:\n%s", s)
	}
	if !strings.Contains(s, "__lv") {
		t.Errorf("expected a fresh __lv* variable in renamed rule, got:\n%s", s)
	}
}

// The return-value variable must be renamed to the SAME fresh name in both
// the head and the body within the same branch.
func TestSimplifyRule_HeadValueVarConsistent(t *testing.T) {
	src := `package test
import rego.v1
foo := x if {
    input.bar[x] == 1
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(module.Rules[0])

	// __lv0 is the fresh name assigned to x; it must appear in both the head
	// ("foo := __lv0") and the body ("equal(input.bar[__lv0], 1)").
	s := renamed.String()
	if strings.Count(s, "__lv0") < 2 {
		t.Errorf("expected __lv0 to appear in both head and body, got:\n%s", s)
	}
}

// Variables with the same name in the main branch and an else branch must
// receive DISTINCT fresh names (they are independent scopes).
func TestSimplifyRule_ElseBranchIndependentRenaming(t *testing.T) {
	src := `package test
import rego.v1
foo := x if {
    input.bar[x] == 1
} else := x if {
    input.baz[x] == 2
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(module.Rules[0])

	if renamed.Else == nil {
		t.Fatal("expected an else branch")
	}

	full := renamed.String()
	elseStr := renamed.Else.String()

	if strings.Contains(full, "x") {
		t.Errorf("original 'x' should not appear after renaming, got:\n%s", full)
	}
	// Main branch uses __lv0; else branch must use a different name (__lv1).
	if strings.Contains(elseStr, "__lv0") {
		t.Errorf("else branch should not contain main branch's __lv0, got:\n%s", elseStr)
	}
	if !strings.Contains(elseStr, "__lv1") {
		t.Errorf("else branch should contain its own fresh name __lv1, got:\n%s", elseStr)
	}
}

// Two else branches (else-if-else) must each get independent fresh names.
func TestSimplifyRule_MultipleElseBranchesIndependent(t *testing.T) {
	src := `package test
import rego.v1
foo := x if {
    input.a[x] == 1
} else := x if {
    input.b[x] == 2
} else := x if {
    input.c[x] == 3
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(module.Rules[0])

	if renamed.Else == nil || renamed.Else.Else == nil {
		t.Fatal("expected two else branches")
	}

	full := renamed.String()
	else2Str := renamed.Else.Else.String()

	if strings.Contains(full, "x") {
		t.Errorf("original 'x' should not appear after renaming, got:\n%s", full)
	}
	// else-2 must use __lv2, not the names from earlier branches.
	if strings.Contains(else2Str, "__lv0") || strings.Contains(else2Str, "__lv1") {
		t.Errorf("else-2 should use its own fresh name, not __lv0/__lv1, got:\n%s", else2Str)
	}
	if !strings.Contains(else2Str, "__lv2") {
		t.Errorf("else-2 should contain __lv2, got:\n%s", else2Str)
	}
}

// Quantified variables must not be renamed.
func TestSimplifyRule_QuantifiedVarsUntouched(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    input.items[i] > 0
}`
	module := mustParseModule(t, src)
	rule := module.Rules[0]
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(rule)

	vars := collectAllVarNames(renamed)
	if vars["i"] == 0 {
		t.Errorf("quantified variable 'i' should not have been renamed, got vars: %v", vars)
	}
}
