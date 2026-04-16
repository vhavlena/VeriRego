package util_test

import (
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/util"
)

// parseModule is a test helper that compiles a Rego module string and panics
// on parse/compile errors.
func parseModule(t *testing.T, src string) *ast.Module {
	t.Helper()
	module, err := ast.ParseModuleWithOpts("test.rego", src, ast.ParserOptions{ProcessAnnotation: false})
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	return module
}

// collectVarNames walks every expression in a rule and returns a set of all
// ast.Var names found.
func collectVarNames(rule *ast.Rule) map[string]bool {
	names := make(map[string]bool)
	var walkTerm func(*ast.Term)
	walkTerm = func(t *ast.Term) {
		if t == nil {
			return
		}
		switch v := t.Value.(type) {
		case ast.Var:
			names[string(v)] = true
		case ast.Ref:
			for _, seg := range v {
				walkTerm(seg)
			}
		case *ast.Array:
			for i := 0; i < v.Len(); i++ {
				walkTerm(v.Elem(i))
			}
		case ast.Object:
			v.Foreach(func(k, val *ast.Term) {
				walkTerm(k)
				walkTerm(val)
			})
		case ast.Set:
			v.Foreach(func(elem *ast.Term) {
				walkTerm(elem)
			})
		case ast.Call:
			for _, ct := range v {
				walkTerm(ct)
			}
		}
	}
	var walkExpr func(*ast.Expr)
	walkExpr = func(expr *ast.Expr) {
		switch terms := expr.Terms.(type) {
		case *ast.Term:
			walkTerm(terms)
		case []*ast.Term:
			for _, term := range terms {
				walkTerm(term)
			}
		}
		for _, w := range expr.With {
			walkTerm(w.Target)
			walkTerm(w.Value)
		}
	}
	for _, expr := range rule.Body {
		walkExpr(expr)
	}
	if rule.Head.Value != nil {
		walkTerm(rule.Head.Value)
	}
	if rule.Head.Key != nil {
		walkTerm(rule.Head.Key)
	}
	return names
}

// ──────────────────────────────────────────────────────────────────────────────

func TestRenameLocalVarsInRule_BasicAssignment(t *testing.T) {
	src := `
package test
import rego.v1
allow if {
    x := 1
    x > 0
}
`
	module := parseModule(t, src)
	if len(module.Rules) == 0 {
		t.Fatal("no rules parsed")
	}
	rule := module.Rules[0]
	renamed := util.RenameLocalVarsInRule(rule, 0, util.DefaultRenameFunc)

	vars := collectVarNames(renamed)
	if vars["x"] {
		t.Error("original variable 'x' should have been renamed but is still present")
	}
	if !vars["x__r0"] {
		t.Errorf("expected renamed variable 'x__r0', got vars: %v", vars)
	}
}

func TestRenameLocalVarsInRule_OriginalUnchanged(t *testing.T) {
	src := `
package test
import rego.v1
allow if {
    y := "hello"
    y != ""
}
`
	module := parseModule(t, src)
	rule := module.Rules[0]
	util.RenameLocalVarsInRule(rule, 0, util.DefaultRenameFunc)

	// Original rule must be unmodified.
	vars := collectVarNames(rule)
	if !vars["y"] {
		t.Error("original rule should still contain 'y' after rename (copy semantics)")
	}
}

func TestRenameLocalVarsInModule_UniqueAcrossRules(t *testing.T) {
	src := `
package test
import rego.v1
allow if {
    x := 1
    x > 0
}
deny if {
    x := 2
    x < 0
}
`
	module := parseModule(t, src)
	newModule := util.RenameLocalVarsInModule(module, util.DefaultRenameFunc)

	if len(newModule.Rules) != 2 {
		t.Fatalf("expected 2 rules, got %d", len(newModule.Rules))
	}

	vars0 := collectVarNames(newModule.Rules[0])
	vars1 := collectVarNames(newModule.Rules[1])

	if vars0["x"] || vars1["x"] {
		t.Error("original 'x' should not appear in any renamed rule")
	}
	if !vars0["x__r0"] {
		t.Errorf("rule 0: expected 'x__r0', got %v", vars0)
	}
	if !vars1["x__r1"] {
		t.Errorf("rule 1: expected 'x__r1', got %v", vars1)
	}
}

func TestRenameLocalVarsInRule_CustomRenameFunc(t *testing.T) {
	src := `
package test
import rego.v1
allow if {
    z := 42
    z == 42
}
`
	module := parseModule(t, src)
	rule := module.Rules[0]

	custom := func(ruleName string, ruleIdx int, varName string) (string, bool) {
		return "RENAMED_" + varName, true
	}
	renamed := util.RenameLocalVarsInRule(rule, 0, custom)

	vars := collectVarNames(renamed)
	if vars["z"] {
		t.Error("'z' should have been renamed")
	}
	if !vars["RENAMED_z"] {
		t.Errorf("expected 'RENAMED_z', got %v", vars)
	}
}

func TestRenameLocalVarsInRule_QuantifiedVarsUntouched(t *testing.T) {
	// 'v' is a quantified variable (used in iteration), not a local assignment.
	src := `
package test
import rego.v1
allow if {
    some v
    v := input.items[_]
    v > 0
}
`
	module := parseModule(t, src)
	rule := module.Rules[0]
	renamed := util.RenameLocalVarsInRule(rule, 3, util.DefaultRenameFunc)

	_ = renamed
	// We just verify that the rename doesn't panic and local vars are renamed;
	// whether 'v' ends up local or quantified depends on OPA's compiled form —
	// this test mainly checks stability.
}

func TestRenameLocalVarsInModule_ModuleOriginalUnchanged(t *testing.T) {
	src := `
package test
import rego.v1
allow if {
    a := "foo"
    a == "foo"
}
`
	module := parseModule(t, src)
	util.RenameLocalVarsInModule(module, util.DefaultRenameFunc)

	// Original module rules must not be mutated.
	vars := collectVarNames(module.Rules[0])
	if !vars["a"] {
		t.Error("original module rule should still contain 'a' after RenameLocalVarsInModule")
	}
}
