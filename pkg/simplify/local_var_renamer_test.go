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

// freshNamesIn returns the set of __lv<N> names found in s.
func freshNamesIn(s string) map[string]bool {
	names := map[string]bool{}
	for {
		idx := strings.Index(s, "__lv")
		if idx < 0 {
			break
		}
		s = s[idx+4:]
		end := 0
		for end < len(s) && s[end] >= '0' && s[end] <= '9' {
			end++
		}
		if end > 0 {
			names["__lv"+s[:end]] = true
		}
		s = s[end:]
	}
	return names
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
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	if strings.Contains(s, "x") {
		t.Errorf("original variable 'x' should have been renamed, got:\n%s", s)
	}
	if !strings.Contains(s, "__lv") {
		t.Errorf("expected a fresh __lv* variable, got:\n%s", s)
	}
}

// All occurrences of the same local variable must map to the SAME fresh name.
func TestSimplifyRule_ConsistentRenaming(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    x := 1
    x > 0
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	// Exactly one distinct fresh name must be used for both occurrences of 'x'.
	if len(freshNamesIn(s)) != 1 {
		t.Errorf("expected exactly 1 fresh name for 'x', got %v", freshNamesIn(s))
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

	if !strings.Contains(rule.String(), "y") {
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

	s0 := newModule.Rules[0].String()
	s1 := newModule.Rules[1].String()

	if strings.Contains(s0, "x") || strings.Contains(s1, "x") {
		t.Error("original 'x' should not appear in any renamed rule")
	}
	fresh0, fresh1 := freshNamesIn(s0), freshNamesIn(s1)
	if len(fresh0) == 0 {
		t.Error("rule 0: expected at least one __lv* variable")
	}
	if len(fresh1) == 0 {
		t.Error("rule 1: expected at least one __lv* variable")
	}
	for n := range fresh0 {
		if fresh1[n] {
			t.Errorf("rules 0 and 1 share fresh variable name %q", n)
		}
	}
}

// Multiple distinct local variables in one rule must each get their own fresh name.
func TestSimplifyRule_MultipleLocals(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    xx := 1
    yy := 2
    xx + yy > 0
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	if strings.Contains(s, "xx") || strings.Contains(s, "yy") {
		t.Errorf("original variables 'xx'/'yy' should have been renamed, got:\n%s", s)
	}
	if len(freshNamesIn(s)) < 2 {
		t.Errorf("expected at least 2 fresh variables for 'xx' and 'yy', got %v", freshNamesIn(s))
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

	if !strings.Contains(module.Rules[0].String(), "z") {
		t.Error("original module rule should still contain 'z' after SimplifyModule")
	}
}

// Each "_" wildcard occurrence must be replaced by a distinct fresh name.
func TestSimplifyRule_WildcardsReplaced(t *testing.T) {
	src := `package test
import rego.v1
foo = true if {
    __local0__ = data.test.sites[_].servers[_].hostname
    gt(__local0__, 3)
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	// OPA compiles each "_" to a "$N" variable; after renaming none should remain.
	if strings.Contains(s, "$") {
		t.Errorf("wildcard '$N' variables should have been replaced, got:\n%s", s)
	}
	if len(freshNamesIn(s)) < 2 {
		t.Errorf("expected at least 2 distinct fresh names for two '_' occurrences, got %v", freshNamesIn(s))
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
	s := r.SimplifyRule(module.Rules[0]).String()

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
	s := r.SimplifyRule(module.Rules[0]).String()

	// __lv0 is the fresh name assigned to x; it must appear in both head and body.
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
	if strings.Contains(else2Str, "__lv0") || strings.Contains(else2Str, "__lv1") {
		t.Errorf("else-2 should use its own fresh name, not __lv0/__lv1, got:\n%s", else2Str)
	}
	if !strings.Contains(else2Str, "__lv2") {
		t.Errorf("else-2 should contain __lv2, got:\n%s", else2Str)
	}
}

// Quantified variables (iteration indices / free variables) must be renamed
// just like local variables.
func TestSimplifyRule_QuantifiedVarsRenamed(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    input.items[kk] > 0
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	if strings.Contains(s, "kk") {
		t.Errorf("quantified variable 'kk' should have been renamed, got:\n%s", s)
	}
	if !strings.Contains(s, "__lv") {
		t.Errorf("expected a fresh __lv* variable replacing 'kk', got:\n%s", s)
	}
}

// Multiple quantified variables must each receive their own distinct fresh name.
func TestSimplifyRule_MultipleQuantifiedVarsRenamed(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    input.items[kk] > 0
    input.other[jj] == "x"
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	if strings.Contains(s, "kk") || strings.Contains(s, "jj") {
		t.Errorf("quantified variables 'kk'/'jj' should have been renamed, got:\n%s", s)
	}
	if len(freshNamesIn(s)) < 2 {
		t.Errorf("expected at least 2 fresh variables for 'kk' and 'jj', got %v", freshNamesIn(s))
	}
}

// A mix of local and quantified variables must all be renamed, each consistently.
func TestSimplifyRule_MixedLocalAndQuantifiedRenamed(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    x := input.items[kk]
    x > 0
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	s := r.SimplifyRule(module.Rules[0]).String()

	if strings.Contains(s, "x") || strings.Contains(s, "kk") {
		t.Errorf("variables 'x'/'kk' should have been renamed, got:\n%s", s)
	}
	if len(freshNamesIn(s)) < 2 {
		t.Errorf("expected at least 2 fresh variables for 'x' and 'kk', got %v", freshNamesIn(s))
	}
}

// Quantified variables in else branches must be renamed independently of the
// main branch (same name in two branches → distinct fresh names).
func TestSimplifyRule_QuantifiedVarsElseBranchIndependent(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    input.items[kk] > 0
} else if {
    input.other[kk] == "x"
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	renamed := r.SimplifyRule(module.Rules[0])

	if renamed.Else == nil {
		t.Fatal("expected an else branch")
	}

	mainStr := renamed.Head.String() + renamed.Body.String()
	elseStr := renamed.Else.String()

	if strings.Contains(mainStr+elseStr, "kk") {
		t.Errorf("quantified variable 'kk' should have been renamed in both branches, got main:%s else:%s", mainStr, elseStr)
	}
	for n := range freshNamesIn(mainStr) {
		if strings.Contains(elseStr, n) {
			t.Errorf("main and else branch share quantified fresh name %q", n)
		}
	}
}

// Cross-rule uniqueness must hold for quantified variables too.
func TestSimplifyModule_QuantifiedCrossRuleUniqueness(t *testing.T) {
	src := `package test
import rego.v1
allow if {
    input.items[kk] > 0
}
deny if {
    input.items[kk] < 0
}`
	module := mustParseModule(t, src)
	r := NewLocalVarRenamer()
	newModule := r.SimplifyModule(module)

	s0 := newModule.Rules[0].String()
	s1 := newModule.Rules[1].String()

	if strings.Contains(s0, "kk") || strings.Contains(s1, "kk") {
		t.Error("quantified variable 'kk' should not appear in any renamed rule")
	}
	fresh0, fresh1 := freshNamesIn(s0), freshNamesIn(s1)
	for n := range fresh0 {
		if fresh1[n] {
			t.Errorf("rules 0 and 1 share quantified fresh variable name %q", n)
		}
	}
}
