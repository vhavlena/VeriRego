package types

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
)

// compileAndGetFirstRule parses src with Rego v1 semantics, compiles it with
// OPA, and returns the first rule of the compiled module.  The test fails
// immediately on any error.
func compileAndGetFirstRule(t *testing.T, src string) *ast.Rule {
	t.Helper()
	mod, err := ast.ParseModuleWithOpts("test.rego", src, ast.ParserOptions{RegoVersion: ast.RegoV1})
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	compiled := compileModule(t, mod)
	if len(compiled.Rules) == 0 {
		t.Fatal("compiled module has no rules")
	}
	return compiled.Rules[0]
}

// hasLocalN reports whether any key in m matches the __localN__ naming pattern
// produced by OPA's compiler.
func hasLocalN(m map[string]bool) bool {
	for name := range m {
		if strings.HasPrefix(name, "__local") && strings.HasSuffix(name, "__") {
			return true
		}
	}
	return false
}

// countLocalN counts how many keys in m match the __localN__ pattern.
func countLocalN(m map[string]bool) int {
	n := 0
	for name := range m {
		if strings.HasPrefix(name, "__local") && strings.HasSuffix(name, "__") {
			n++
		}
	}
	return n
}

// ---- disjointness invariant ------------------------------------------------

func TestClassifyVars_SetsAreDisjoint(t *testing.T) {
	// No variable should appear in both Local and Quantified.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	user := input.user
	data.users[uid]
	uid != user
}`)

	vc := ClassifyVars(rule)
	for name := range vc.Local {
		if vc.Quantified[name] {
			t.Errorf("variable %q appears in both Local and Quantified", name)
		}
	}
}

// ---- local variables (OPA-generated __localN__ temporaries) ----------------

func TestClassifyVars_CompilerGeneratedLocals(t *testing.T) {
	// OPA's compiler introduces __localN__ temporaries for sub-expressions.
	// For example, x := "hello" compiles to  __local0__ = "hello".
	// These temporaries should be classified as local.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	x := "hello"
	x == "hello"
}`)

	vc := ClassifyVars(rule)

	// At least one __localN__ must be in Local, none in Quantified.
	if !hasLocalN(vc.Local) {
		t.Errorf("expected at least one __localN__ to be local; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
	if hasLocalN(vc.Quantified) {
		t.Errorf("unexpected __localN__ in quantified set; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
}

func TestClassifyVars_MultipleLocalTemporaries(t *testing.T) {
	// Multiple user-assigned variables should each produce a local __localN__.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	x := input.name
	y := input.age
	x == "admin"
	y > 0
}`)

	vc := ClassifyVars(rule)

	// Expect at least two local __localN__ temporaries (x and y).
	n := countLocalN(vc.Local)
	if n < 2 {
		t.Errorf("expected ≥2 local __localN__ temporaries, got %d; local=%v quantified=%v", n, vc.Local, vc.Quantified)
	}
}

// ---- quantified variables: named ref indices (survive compilation) ----------

func TestClassifyVars_RefIndexQuantified(t *testing.T) {
	// data.users[uid] — uid appears as a non-ground ref index and is not
	// renamed by the compiler, so it remains "uid" and must be quantified.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	data.users[uid]
	uid != "guest"
}`)

	vc := ClassifyVars(rule)

	if !vc.IsQuantified("uid") {
		t.Errorf("expected uid to be quantified; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
	if vc.IsLocal("uid") {
		t.Errorf("expected uid NOT to be local")
	}
}

func TestClassifyVars_MultiLevelRefIndex(t *testing.T) {
	// data.matrix[i][j] — both i and j are non-ground ref indices and are
	// kept under their original names by the compiler.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	data.matrix[i][j]
	i != j
}`)

	vc := ClassifyVars(rule)

	for _, name := range []string{"i", "j"} {
		if !vc.IsQuantified(name) {
			t.Errorf("expected %s to be quantified; local=%v quantified=%v", name, vc.Local, vc.Quantified)
		}
		if vc.IsLocal(name) {
			t.Errorf("expected %s NOT to be local", name)
		}
	}
}

// ---- quantified variables: compiled iteration (some x in coll) -------------

// OPA compiles "some role in data.roles" to:
//
//	__localV__ = data.roles[__localK__]
//
// __localK__ is the ref index → quantified.
// __localV__ is the LHS variable receiving the fetched value → local.
func TestClassifyVars_SomeInCollection(t *testing.T) {
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	some role in data.roles
	role == "admin"
}`)

	vc := ClassifyVars(rule)

	// Exactly one __localN__ quantified (the ref index).
	nQ := countLocalN(vc.Quantified)
	if nQ < 1 {
		t.Errorf("expected ≥1 quantified __localN__ (ref index from some...in); got %d; local=%v quantified=%v", nQ, vc.Local, vc.Quantified)
	}
	// At least one __localN__ local (the value variable).
	nL := countLocalN(vc.Local)
	if nL < 1 {
		t.Errorf("expected ≥1 local __localN__ (value from some...in); got %d; local=%v quantified=%v", nL, vc.Local, vc.Quantified)
	}
}

// OPA compiles "some k, v in data.permissions" to:
//
//	__local1__ = data.permissions[__local0__]
//
// __local0__ (ref index / key) → quantified.
// __local1__ (LHS value) → local.
func TestClassifyVars_SomeKeyValueInObject(t *testing.T) {
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	some k, v in data.permissions
	k == input.action
	v == true
}`)

	vc := ClassifyVars(rule)

	// __local0__ (key/index) should be quantified.
	nQ := countLocalN(vc.Quantified)
	if nQ < 1 {
		t.Errorf("expected ≥1 quantified __localN__ (key/index) for some k,v in; got %d; local=%v quantified=%v", nQ, vc.Local, vc.Quantified)
	}
	// __local1__ (value) should be local.
	nL := countLocalN(vc.Local)
	if nL < 1 {
		t.Errorf("expected ≥1 local __localN__ (value) for some k,v in; got %d; local=%v quantified=%v", nL, vc.Local, vc.Quantified)
	}
}

// ---- quantified variables: partial rule head key ---------------------------

func TestClassifyVars_PartialSetHeadKey(t *testing.T) {
	// "roles contains role if { ... }" — the head key variable (compiled to
	// __localN__ or a $N special variable) must be quantified.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
roles contains role if {
	role := data.all_roles[_]
	role != "guest"
}`)

	vc := ClassifyVars(rule)

	// The head key is compiled to __local0__ (or similar) and should be
	// quantified; nothing should end up in local.
	if len(vc.Quantified) == 0 {
		t.Errorf("expected at least one quantified variable for partial-set head key; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
	if len(vc.Local) != 0 {
		t.Errorf("expected local set to be empty; local=%v", vc.Local)
	}
}

// ---- wildcard exclusion ----------------------------------------------------

func TestClassifyVars_WildcardExcluded(t *testing.T) {
	// The anonymous "_" wildcard must not appear in either set.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	data.items[_]
}`)

	vc := ClassifyVars(rule)

	if vc.IsLocal("_") {
		t.Errorf("expected _ NOT to be in Local")
	}
	if vc.IsQuantified("_") {
		t.Errorf("expected _ NOT to be in Quantified")
	}
}

func TestClassifyVars_NamespaceRootsExcluded(t *testing.T) {
	// "data" and "input" are top-level namespace roots, not variables.
	// They must not appear in either classification set.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	data.users[uid]
	uid == input.user
}`)

	vc := ClassifyVars(rule)

	for _, name := range []string{"data", "input"} {
		if vc.IsLocal(name) {
			t.Errorf("expected %s NOT to be in Local", name)
		}
		if vc.IsQuantified(name) {
			t.Errorf("expected %s NOT to be in Quantified", name)
		}
	}
}

// ---- quantified takes precedence -------------------------------------------

func TestClassifyVars_QuantifiedTakesPrecedence(t *testing.T) {
	// uid appears both as a ref index (quantified) and in an equality
	// constraint: the quantified classification must win.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	data.users[uid]
	uid == input.user
}`)

	vc := ClassifyVars(rule)

	if !vc.IsQuantified("uid") {
		t.Errorf("expected uid to be quantified; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
	if vc.IsLocal("uid") {
		t.Errorf("expected uid NOT to be local (quantified takes precedence)")
	}
}

// ---- combined scenario -----------------------------------------------------

func TestClassifyVars_NamedRefIndexWithLocalTemporary(t *testing.T) {
	// Named ref-index variable (uid, survives compilation) is quantified;
	// the compiler-generated temporary from the comparison is local.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
allow if {
	data.users[uid]
	uid != "guest"
	age := input.age
	age > 18
}`)

	vc := ClassifyVars(rule)

	// uid is a named ref index → quantified.
	if !vc.IsQuantified("uid") {
		t.Errorf("expected uid to be quantified; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
	// At least one __localN__ from the age assignment → local.
	if !hasLocalN(vc.Local) {
		t.Errorf("expected at least one __localN__ to be local; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
}

func TestClassifyVars_ElseBranchVars(t *testing.T) {
	// Variables in an else branch must be classified too.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
result := "admin" if {
	input.role == "admin"
} else := "user" if {
	data.roles[role]
	role == input.role
}`)

	vc := ClassifyVars(rule)

	// "role" appears as a ref index in the else branch → quantified.
	if !vc.IsQuantified("role") {
		t.Errorf("expected else-branch 'role' to be quantified; local=%v quantified=%v", vc.Local, vc.Quantified)
	}
}

// ---- parameter variables ---------------------------------------------------

// paramNamesFromArgs returns the set of variable names found in rule.Head.Args.
// OPA's compiler renames source-level parameter names to __localN__ temporaries,
// so tests must inspect the compiled names rather than the source names.
func paramNamesFromArgs(rule *ast.Rule) map[string]bool {
	m := make(map[string]bool)
	for _, arg := range rule.Head.Args {
		if v, ok := arg.Value.(ast.Var); ok {
			m[string(v)] = true
		}
	}
	return m
}

func TestClassifyVars_FunctionParamIsParameter(t *testing.T) {
	// Parameters declared in the rule head must land in Parameter, not in
	// Local or Quantified.  OPA renames source params to __localN__ temporaries.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
is_admin(user) if {
	user == "admin"
}`)

	params := paramNamesFromArgs(rule)
	if len(params) == 0 {
		t.Fatal("expected at least one compiled parameter in rule.Head.Args")
	}

	vc := ClassifyVars(rule)

	for name := range params {
		if !vc.IsParameter(name) {
			t.Errorf("expected %q (compiled param) to be a parameter; local=%v quantified=%v parameter=%v", name, vc.Local, vc.Quantified, vc.Parameter)
		}
		if vc.IsLocal(name) {
			t.Errorf("expected %q NOT to be local", name)
		}
		if vc.IsQuantified(name) {
			t.Errorf("expected %q NOT to be quantified", name)
		}
	}
}

func TestClassifyVars_MultipleParamsAreParameter(t *testing.T) {
	// All parameters from a multi-arg function must be in Parameter.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
has_role(user, role) if {
	data.roles[user] == role
}`)

	params := paramNamesFromArgs(rule)
	if len(params) < 2 {
		t.Fatalf("expected 2 compiled parameters in rule.Head.Args, got %d", len(params))
	}

	vc := ClassifyVars(rule)

	for name := range params {
		if !vc.IsParameter(name) {
			t.Errorf("expected %q (compiled param) to be a parameter; local=%v quantified=%v parameter=%v", name, vc.Local, vc.Quantified, vc.Parameter)
		}
		if vc.IsLocal(name) {
			t.Errorf("expected %q NOT to be local", name)
		}
		if vc.IsQuantified(name) {
			t.Errorf("expected %q NOT to be quantified", name)
		}
	}
}

func TestClassifyVars_ParamNotInLocalOrQuantified(t *testing.T) {
	// A parameter used as a head return value (foo(x) := x) must still be
	// classified as parameter, not as local.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
identity(x) := x`)

	params := paramNamesFromArgs(rule)
	if len(params) == 0 {
		t.Fatal("expected at least one compiled parameter in rule.Head.Args")
	}

	vc := ClassifyVarsBranch(rule)

	for name := range params {
		if !vc.IsParameter(name) {
			t.Errorf("expected %q (compiled param) to be a parameter; local=%v quantified=%v parameter=%v", name, vc.Local, vc.Quantified, vc.Parameter)
		}
		if vc.IsLocal(name) {
			t.Errorf("expected %q NOT to be local", name)
		}
		if vc.IsQuantified(name) {
			t.Errorf("expected %q NOT to be quantified", name)
		}
	}
}

func TestClassifyVars_SetsAreDisjointWithParameter(t *testing.T) {
	// No variable should appear in more than one of Local, Quantified, Parameter.
	t.Parallel()
	rule := compileAndGetFirstRule(t, `package test
import rego.v1
check(user) if {
	x := input.age
	data.users[uid]
	uid != user
	x > 0
}`)

	vc := ClassifyVars(rule)

	for name := range vc.Local {
		if vc.Quantified[name] {
			t.Errorf("variable %q in both Local and Quantified", name)
		}
		if vc.Parameter[name] {
			t.Errorf("variable %q in both Local and Parameter", name)
		}
	}
	for name := range vc.Quantified {
		if vc.Parameter[name] {
			t.Errorf("variable %q in both Quantified and Parameter", name)
		}
	}
}
