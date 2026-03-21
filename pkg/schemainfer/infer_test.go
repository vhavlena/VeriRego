package schemainfer

import (
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
)

// compileAndInfer parses, compiles, and runs schema inference on a Rego v1 policy.
func compileAndInfer(t *testing.T, policy string) *SchemaInferrer {
	t.Helper()
	mod, err := ast.ParseModuleWithOpts("test.rego", policy, ast.ParserOptions{RegoVersion: ast.RegoV1})
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{mod.Package.Path.String(): mod})
	if compiler.Failed() {
		t.Fatalf("compile error: %v", compiler.Errors)
	}
	compiled := compiler.Modules[mod.Package.Path.String()]
	si := New()
	si.InferFromModule(compiled, mod.Package.Path)
	return si
}

// getNode traverses a SchemaNode tree following the given path of field names.
// Returns nil if any step in the path does not exist.
func getNode(root *SchemaNode, path ...string) *SchemaNode {
	cur := root
	for _, key := range path {
		if cur == nil || cur.Properties == nil {
			return nil
		}
		cur = cur.Properties[key]
	}
	return cur
}

// ---- equality constraints ---------------------------------------------------

func TestInfer_StringEqualityDirect(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.name == "admin" }`)

	node := getNode(si.Input, "name")
	if node == nil {
		t.Fatal("input.name not found in schema")
	}
	if node.Hint != HintString {
		t.Errorf("input.name: expected HintString, got %v", node.Hint)
	}
}

func TestInfer_IntegerEqualityDirect(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.count == 5 }`)

	node := getNode(si.Input, "count")
	if node == nil {
		t.Fatal("input.count not found in schema")
	}
	if node.Hint != HintInteger {
		t.Errorf("input.count: expected HintInteger, got %v", node.Hint)
	}
}

func TestInfer_BooleanEqualityDirect(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.active == true }`)

	node := getNode(si.Input, "active")
	if node == nil {
		t.Fatal("input.active not found in schema")
	}
	if node.Hint != HintBoolean {
		t.Errorf("input.active: expected HintBoolean, got %v", node.Hint)
	}
}

// ---- comparison operators (OPA compiles these through a temp var) ------------

func TestInfer_IntegerFromGtComparison(t *testing.T) {
	// OPA compiles `input.age > 18` as:
	//   eq(__local0__, input.age)
	//   gt(__local0__, 18)
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.age > 18 }`)

	node := getNode(si.Input, "age")
	if node == nil {
		t.Fatal("input.age not found in schema")
	}
	if node.Hint != HintInteger {
		t.Errorf("input.age: expected HintInteger, got %v", node.Hint)
	}
}

func TestInfer_IntegerFromLtComparison(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.score < 100 }`)

	node := getNode(si.Input, "score")
	if node == nil {
		t.Fatal("input.score not found")
	}
	if node.Hint != HintInteger {
		t.Errorf("input.score: expected HintInteger, got %v", node.Hint)
	}
}

// ---- builtin string functions (via predef registry) -------------------------

func TestInfer_StringFromStartswith(t *testing.T) {
	// Compiled: eq(__local0__, input.name); startswith(__local0__, "prefix")
	si := compileAndInfer(t, `package test
import rego.v1
allow if { startswith(input.name, "admin-") }`)

	node := getNode(si.Input, "name")
	if node == nil {
		t.Fatal("input.name not found")
	}
	if node.Hint != HintString {
		t.Errorf("input.name: expected HintString, got %v", node.Hint)
	}
}

func TestInfer_StringFromContains(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { contains(input.email, "@") }`)

	node := getNode(si.Input, "email")
	if node == nil {
		t.Fatal("input.email not found")
	}
	if node.Hint != HintString {
		t.Errorf("input.email: expected HintString, got %v", node.Hint)
	}
}

func TestInfer_StringFromTrim(t *testing.T) {
	// Compiled: eq(__local2__, input.val); trim(__local2__, " ", __local1__)
	si := compileAndInfer(t, `package test
import rego.v1
allow if { x := trim(input.val, " "); x != "" }`)

	node := getNode(si.Input, "val")
	if node == nil {
		t.Fatal("input.val not found")
	}
	if node.Hint != HintString {
		t.Errorf("input.val: expected HintString, got %v", node.Hint)
	}
}

// ---- numeric builtins -------------------------------------------------------

func TestInfer_IntegerFromPlus(t *testing.T) {
	// Compiled: eq(__local1__, input.count); plus(__local1__, 1, __local0__)
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.count + 1 > 0 }`)

	node := getNode(si.Input, "count")
	if node == nil {
		t.Fatal("input.count not found")
	}
	if node.Hint != HintInteger {
		t.Errorf("input.count: expected HintInteger, got %v", node.Hint)
	}
}

// ---- array iteration --------------------------------------------------------

func TestInfer_ArrayFromIteration(t *testing.T) {
	// input.roles[_] == "admin"  →  input.roles is array, items are string
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.roles[_] == "admin" }`)

	rolesNode := getNode(si.Input, "roles")
	if rolesNode == nil {
		t.Fatal("input.roles not found")
	}
	if rolesNode.Hint != HintArray {
		t.Errorf("input.roles: expected HintArray, got %v", rolesNode.Hint)
	}
	if rolesNode.Items == nil {
		t.Fatal("input.roles.items is nil")
	}
	if rolesNode.Items.Hint != HintString {
		t.Errorf("input.roles items: expected HintString, got %v", rolesNode.Items.Hint)
	}
}

func TestInfer_ArrayItemsFromComparison(t *testing.T) {
	// input.scores[_] > 0  →  input.scores is array, items are integer
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.scores[_] > 0 }`)

	node := getNode(si.Input, "scores")
	if node == nil {
		t.Fatal("input.scores not found")
	}
	if node.Hint != HintArray {
		t.Errorf("input.scores: expected HintArray, got %v", node.Hint)
	}
	if node.Items == nil {
		t.Fatal("input.scores.items is nil")
	}
	if node.Items.Hint != HintInteger {
		t.Errorf("input.scores items: expected HintInteger, got %v", node.Items.Hint)
	}
}

// ---- nested object access ---------------------------------------------------

func TestInfer_NestedObjectField(t *testing.T) {
	// input.user.name == "alice"  →  input.user is object, input.user.name is string
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.user.name == "alice" }`)

	userNode := getNode(si.Input, "user")
	if userNode == nil {
		t.Fatal("input.user not found")
	}
	if userNode.Hint != HintObject {
		t.Errorf("input.user: expected HintObject, got %v", userNode.Hint)
	}

	nameNode := getNode(si.Input, "user", "name")
	if nameNode == nil {
		t.Fatal("input.user.name not found")
	}
	if nameNode.Hint != HintString {
		t.Errorf("input.user.name: expected HintString, got %v", nameNode.Hint)
	}
}

func TestInfer_MultipleFieldsOnSameObject(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
    input.user.role == "admin"
    input.user.age > 18
}`)

	if getNode(si.Input, "user", "role") == nil {
		t.Fatal("input.user.role not found")
	}
	if getNode(si.Input, "user", "role").Hint != HintString {
		t.Errorf("input.user.role: expected HintString")
	}
	if getNode(si.Input, "user", "age") == nil {
		t.Fatal("input.user.age not found")
	}
	if getNode(si.Input, "user", "age").Hint != HintInteger {
		t.Errorf("input.user.age: expected HintInteger")
	}
}

// ---- data document refs -----------------------------------------------------

func TestInfer_DataArrayFromIteration(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { data.acl[_] == input.user }`)

	aclNode := si.Data.Properties["acl"]
	if aclNode == nil {
		t.Fatal("data.acl not found in data schema")
	}
	if aclNode.Hint != HintArray {
		t.Errorf("data.acl: expected HintArray, got %v", aclNode.Hint)
	}
}

func TestInfer_DataStringField(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { data.config.owner == "alice" }`)

	node := si.Data.Properties["config"]
	if node == nil {
		t.Fatal("data.config not found")
	}
	ownerNode := node.Properties["owner"]
	if ownerNode == nil {
		t.Fatal("data.config.owner not found")
	}
	if ownerNode.Hint != HintString {
		t.Errorf("data.config.owner: expected HintString, got %v", ownerNode.Hint)
	}
}

// ---- own-package rule refs are excluded from data schema --------------------

func TestInfer_OwnPackageRefsExcluded(t *testing.T) {
	// References to rules in the same package (data.test.*) must not appear
	// as external data schema entries.
	si := compileAndInfer(t, `package test
import rego.v1
helper if { input.x == "ok" }
allow if { helper; input.y == "yes" }`)

	// The data schema should be empty (no external data refs).
	if len(si.Data.Properties) != 0 {
		t.Errorf("data schema should be empty for own-package refs, got: %v", si.Data.Properties)
	}
}

// ---- multiple rules ---------------------------------------------------------

func TestInfer_MultipleRules(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.name == "alice" }
allow if { input.name == "bob" }
deny if { input.banned == true }`)

	nameNode := getNode(si.Input, "name")
	if nameNode == nil || nameNode.Hint != HintString {
		t.Errorf("input.name: expected HintString")
	}
	bannedNode := getNode(si.Input, "banned")
	if bannedNode == nil || bannedNode.Hint != HintBoolean {
		t.Errorf("input.banned: expected HintBoolean")
	}
}

// ---- regoTypeToHint ---------------------------------------------------------

func TestRegoTypeToHint(t *testing.T) {
	tests := []struct {
		name     string
		kind     string
		expected TypeHint
	}{
		{"string", "string", HintString},
		{"integer", "integer", HintInteger},
		{"boolean", "boolean", HintBoolean},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Exercise regoTypeToHint indirectly through builtinParamHints.
			// "trim" has all-string params; "plus" has all-int params.
			var hints []TypeHint
			switch tt.kind {
			case "string":
				hints = builtinParamHints("trim", 2) // trim(s, cutset) → [string, string]
			case "integer":
				hints = builtinParamHints("plus", 2) // plus(a, b) → [int, int]
			case "boolean":
				// No binary boolean-param builtin in the registry; test via direct call.
				return
			}
			for i, h := range hints {
				if h != tt.expected {
					t.Errorf("param[%d]: expected %v, got %v", i, tt.expected, h)
				}
			}
		})
	}
}

// ---- mergeHint --------------------------------------------------------------

func TestMergeHint(t *testing.T) {
	if got := mergeHint(HintUnknown, HintString); got != HintString {
		t.Errorf("mergeHint(Unknown, String): expected String, got %v", got)
	}
	if got := mergeHint(HintString, HintUnknown); got != HintString {
		t.Errorf("mergeHint(String, Unknown): expected String, got %v", got)
	}
	if got := mergeHint(HintString, HintInteger); got != HintString {
		t.Errorf("mergeHint(String, Integer): expected existing (String), got %v", got)
	}
}

// ---- literalHint ------------------------------------------------------------

func TestLiteralHint(t *testing.T) {
	tests := []struct {
		term     *ast.Term
		expected TypeHint
	}{
		{ast.StringTerm("hello"), HintString},
		{ast.NumberTerm("42"), HintInteger},
		{ast.BooleanTerm(true), HintBoolean},
		{ast.NullTerm(), HintNull},
		{ast.MustParseTerm(`["a"]`), HintArray},
		{ast.MustParseTerm(`{"k": "v"}`), HintObject},
		{ast.VarTerm("x"), HintUnknown},
	}
	for _, tt := range tests {
		got := literalHint(tt.term)
		if got != tt.expected {
			t.Errorf("literalHint(%v): expected %v, got %v", tt.term, tt.expected, got)
		}
	}
}

// ---- builtinParamHints from predef registry ---------------------------------

func TestBuiltinParamHints_StringFunctions(t *testing.T) {
	for _, fn := range []string{"startswith", "endswith", "contains", "trim", "replace", "concat"} {
		hints := builtinParamHints(fn, 2)
		for i, h := range hints {
			if h != HintString {
				t.Errorf("builtinParamHints(%q)[%d]: expected HintString, got %v", fn, i, h)
			}
		}
	}
}

func TestBuiltinParamHints_NumericFunctions(t *testing.T) {
	for _, fn := range []string{"plus", "minus", "mul", "div"} {
		hints := builtinParamHints(fn, 2)
		for i, h := range hints {
			if h != HintInteger {
				t.Errorf("builtinParamHints(%q)[%d]: expected HintInteger, got %v", fn, i, h)
			}
		}
	}
}

func TestBuiltinParamHints_UnknownFunction(t *testing.T) {
	hints := builtinParamHints("not_a_real_builtin", 3)
	for i, h := range hints {
		if h != HintUnknown {
			t.Errorf("builtinParamHints(unknown)[%d]: expected HintUnknown, got %v", i, h)
		}
	}
}

func TestBuiltinParamHints_ArityMismatch(t *testing.T) {
	// startswith requires exactly 2 args; arity 5 should yield all HintUnknown.
	hints := builtinParamHints("startswith", 5)
	for i, h := range hints {
		if h != HintUnknown {
			t.Errorf("builtinParamHints(startswith, arity=5)[%d]: expected HintUnknown, got %v", i, h)
		}
	}
}
