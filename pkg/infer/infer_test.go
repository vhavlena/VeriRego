package infer

import (
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
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

// assertKind fails the test if node's effective kind does not match wantKind.
func assertKind(t *testing.T, node *SchemaNode, wantKind types.TypeKind) {
	t.Helper()
	et := effectiveType(node)
	if et.Kind != wantKind {
		t.Errorf("expected kind %q, got %q (hint: %s)", wantKind, et.Kind, node.Hint.PrettyPrint())
	}
}

// assertAtomicType fails the test if node's hint is not the given atomic type.
func assertAtomicType(t *testing.T, node *SchemaNode, wantAtom types.AtomicType) {
	t.Helper()
	if node.Hint.Kind != types.KindAtomic || node.Hint.AtomicType != wantAtom {
		t.Errorf("expected atomic type %q, got %s", wantAtom, node.Hint.PrettyPrint())
	}
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
	assertAtomicType(t, node, types.AtomicString)
}

func TestInfer_IntegerEqualityDirect(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.count == 5 }`)

	node := getNode(si.Input, "count")
	if node == nil {
		t.Fatal("input.count not found in schema")
	}
	assertAtomicType(t, node, types.AtomicInt)
}

func TestInfer_BooleanEqualityDirect(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.active == true }`)

	node := getNode(si.Input, "active")
	if node == nil {
		t.Fatal("input.active not found in schema")
	}
	assertAtomicType(t, node, types.AtomicBoolean)
}

// ---- comparison operators (OPA compiles these through a temp var) ------------

func TestInfer_IntegerFromGtComparison(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.age > 18 }`)

	node := getNode(si.Input, "age")
	if node == nil {
		t.Fatal("input.age not found in schema")
	}
	assertAtomicType(t, node, types.AtomicInt)
}

func TestInfer_IntegerFromLtComparison(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.score < 100 }`)

	node := getNode(si.Input, "score")
	if node == nil {
		t.Fatal("input.score not found")
	}
	assertAtomicType(t, node, types.AtomicInt)
}

// ---- builtin string functions (via predef registry) -------------------------

func TestInfer_StringFromStartswith(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { startswith(input.name, "admin-") }`)

	node := getNode(si.Input, "name")
	if node == nil {
		t.Fatal("input.name not found")
	}
	assertAtomicType(t, node, types.AtomicString)
}

func TestInfer_StringFromContains(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { contains(input.email, "@") }`)

	node := getNode(si.Input, "email")
	if node == nil {
		t.Fatal("input.email not found")
	}
	assertAtomicType(t, node, types.AtomicString)
}

// Tests for the assigned form: z := startswith(input.user, "admin")
// OPA compiles this to a 3-arg call startswith(input.user, "admin", z),
// so arity-2-only CheckArity must not silently drop the type hints.

func TestInfer_StringFromStartswithAssigned(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
	z := startswith(input.user, "admin")
	z == true
}`)

	node := getNode(si.Input, "user")
	if node == nil {
		t.Fatal("input.user not found in schema")
	}
	assertAtomicType(t, node, types.AtomicString)
}

func TestInfer_StringFromStartswithResult(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
	input.test == startswith(input.user, "admin")
}`)

	node := getNode(si.Input, "test")
	if node == nil {
		t.Fatal("input.test not found in schema")
	}
	assertAtomicType(t, node, types.AtomicBoolean)
}

func TestInfer_StringFromEndswithAssigned(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
	z := endswith(input.path, "/admin")
	z == true
}`)

	node := getNode(si.Input, "path")
	if node == nil {
		t.Fatal("input.path not found in schema")
	}
	assertAtomicType(t, node, types.AtomicString)
}

func TestInfer_StringFromContainsAssigned(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
	z := contains(input.email, "@")
	z == true
}`)

	node := getNode(si.Input, "email")
	if node == nil {
		t.Fatal("input.email not found in schema")
	}
	assertAtomicType(t, node, types.AtomicString)
}

func TestInfer_StringFromTrim(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { x := trim(input.val, " "); x != "" }`)

	node := getNode(si.Input, "val")
	if node == nil {
		t.Fatal("input.val not found")
	}
	assertAtomicType(t, node, types.AtomicString)
}

// ---- numeric builtins -------------------------------------------------------

func TestInfer_IntegerFromPlus(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.count + 1 > 0 }`)

	node := getNode(si.Input, "count")
	if node == nil {
		t.Fatal("input.count not found")
	}
	assertAtomicType(t, node, types.AtomicInt)
}

// ---- array iteration --------------------------------------------------------

func TestInfer_ArrayFromIteration(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.roles[_] == "admin" }`)

	rolesNode := getNode(si.Input, "roles")
	if rolesNode == nil {
		t.Fatal("input.roles not found")
	}
	assertKind(t, rolesNode, types.KindArray)
	if rolesNode.Items == nil {
		t.Fatal("input.roles.items is nil")
	}
	assertAtomicType(t, rolesNode.Items, types.AtomicString)
}

func TestInfer_ArrayItemsFromComparison(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.scores[_] > 0 }`)

	node := getNode(si.Input, "scores")
	if node == nil {
		t.Fatal("input.scores not found")
	}
	assertKind(t, node, types.KindArray)
	if node.Items == nil {
		t.Fatal("input.scores.items is nil")
	}
	assertAtomicType(t, node.Items, types.AtomicInt)
}

// ---- nested object access ---------------------------------------------------

func TestInfer_NestedObjectField(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { input.user.name == "alice" }`)

	userNode := getNode(si.Input, "user")
	if userNode == nil {
		t.Fatal("input.user not found")
	}
	assertKind(t, userNode, types.KindObject)

	nameNode := getNode(si.Input, "user", "name")
	if nameNode == nil {
		t.Fatal("input.user.name not found")
	}
	assertAtomicType(t, nameNode, types.AtomicString)
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
	assertAtomicType(t, getNode(si.Input, "user", "role"), types.AtomicString)

	if getNode(si.Input, "user", "age") == nil {
		t.Fatal("input.user.age not found")
	}
	assertAtomicType(t, getNode(si.Input, "user", "age"), types.AtomicInt)
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
	assertKind(t, aclNode, types.KindArray)
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
	assertAtomicType(t, ownerNode, types.AtomicString)
}

// ---- own-package rule refs are excluded from data schema --------------------

func TestInfer_OwnPackageRefsExcluded(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
helper if { input.x == "ok" }
allow if { helper; input.y == "yes" }`)

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
	if nameNode == nil {
		t.Fatal("input.name not found")
	}
	assertAtomicType(t, nameNode, types.AtomicString)

	bannedNode := getNode(si.Input, "banned")
	if bannedNode == nil {
		t.Fatal("input.banned not found")
	}
	assertAtomicType(t, bannedNode, types.AtomicBoolean)
}

// ---- mergeType --------------------------------------------------------------

func TestMergeType(t *testing.T) {
	unknown := types.NewUnknownType()
	str := types.NewAtomicType(types.AtomicString)
	integer := types.NewAtomicType(types.AtomicInt)

	got := mergeType(unknown, str)
	if got.Kind != types.KindAtomic || got.AtomicType != types.AtomicString {
		t.Errorf("mergeType(unknown, string): expected string, got %s", got.PrettyPrint())
	}
	got = mergeType(str, unknown)
	if got.Kind != types.KindAtomic || got.AtomicType != types.AtomicString {
		t.Errorf("mergeType(string, unknown): expected string, got %s", got.PrettyPrint())
	}
	got = mergeType(str, integer)
	if got.Kind != types.KindAtomic || got.AtomicType != types.AtomicString {
		t.Errorf("mergeType(string, integer): expected existing (string), got %s", got.PrettyPrint())
	}
}

// ---- LiteralTermType (via types package) ------------------------------------

func TestLiteralTermType(t *testing.T) {
	tests := []struct {
		term     *ast.Term
		wantKind types.TypeKind
		wantAtom types.AtomicType
	}{
		{ast.StringTerm("hello"), types.KindAtomic, types.AtomicString},
		{ast.NumberTerm("42"), types.KindAtomic, types.AtomicInt},
		{ast.BooleanTerm(true), types.KindAtomic, types.AtomicBoolean},
		{ast.NullTerm(), types.KindAtomic, types.AtomicNull},
		{ast.MustParseTerm(`["a"]`), types.KindArray, ""},
		{ast.MustParseTerm(`{"k": "v"}`), types.KindObject, ""},
		{ast.VarTerm("x"), types.KindUnknown, ""},
	}
	for _, tt := range tests {
		got := types.LiteralTermType(tt.term)
		if got.Kind != tt.wantKind {
			t.Errorf("LiteralTermType(%v): expected kind %q, got %q", tt.term, tt.wantKind, got.Kind)
		}
		if tt.wantAtom != "" && got.AtomicType != tt.wantAtom {
			t.Errorf("LiteralTermType(%v): expected atom %q, got %q", tt.term, tt.wantAtom, got.AtomicType)
		}
	}
}

// ---- builtinParamHints from predef registry ---------------------------------

func TestBuiltinParamHints_StringFunctions(t *testing.T) {
	for _, fn := range []string{"startswith", "endswith", "contains", "trim"} {
		hints := builtinParamHints(fn, 2)
		for i, h := range hints {
			if h.Kind != types.KindAtomic || h.AtomicType != types.AtomicString {
				t.Errorf("builtinParamHints(%q)[%d]: expected string, got %s", fn, i, h.PrettyPrint())
			}
		}
	}
}

func TestBuiltinParamHints_NumericFunctions(t *testing.T) {
	for _, fn := range []string{"plus", "minus", "mul", "div"} {
		hints := builtinParamHints(fn, 2)
		for i, h := range hints {
			if h.Kind != types.KindAtomic || h.AtomicType != types.AtomicInt {
				t.Errorf("builtinParamHints(%q)[%d]: expected int, got %s", fn, i, h.PrettyPrint())
			}
		}
	}
}

func TestBuiltinParamHints_UnknownFunction(t *testing.T) {
	hints := builtinParamHints("not_a_real_builtin", 3)
	for i, h := range hints {
		if !h.IsUnknown() {
			t.Errorf("builtinParamHints(unknown)[%d]: expected unknown, got %s", i, h.PrettyPrint())
		}
	}
}

func TestBuiltinParamHints_ArityMismatch(t *testing.T) {
	hints := builtinParamHints("startswith", 5)
	for i, h := range hints {
		if !h.IsUnknown() {
			t.Errorf("builtinParamHints(startswith, arity=5)[%d]: expected unknown, got %s", i, h.PrettyPrint())
		}
	}
}

// ---- IsEqualityOp / IsNumericCompOp (via types package) ---------------------

func TestIsEqualityOp(t *testing.T) {
	for _, op := range []string{"eq", "assign", "unify"} {
		if !types.IsEqualityOp(op) {
			t.Errorf("IsEqualityOp(%q): expected true", op)
		}
	}
	for _, op := range []string{"gt", "lt", "plus", "startswith"} {
		if types.IsEqualityOp(op) {
			t.Errorf("IsEqualityOp(%q): expected false", op)
		}
	}
}

func TestIsNumericCompOp(t *testing.T) {
	for _, op := range []string{"gt", "lt", "gte", "lte"} {
		if !types.IsNumericCompOp(op) {
			t.Errorf("IsNumericCompOp(%q): expected true", op)
		}
	}
	for _, op := range []string{"eq", "plus", "startswith"} {
		if types.IsNumericCompOp(op) {
			t.Errorf("IsNumericCompOp(%q): expected false", op)
		}
	}
}

// ---- dynamic key object access (data.x[input.key] / data.x[role]) -----------

func TestInfer_DynamicKeyFromInputRef(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { data.users[input.user].active == true }`)

	usersNode := si.Data.Properties["users"]
	if usersNode == nil {
		t.Fatal("data.users not found")
	}
	assertKind(t, usersNode, types.KindObject)
	if usersNode.AdditionalProperties == nil {
		t.Fatal("data.users.AdditionalProperties is nil; expected dynamic-key object")
	}

	userNode := getNode(si.Input, "user")
	if userNode == nil {
		t.Fatal("input.user not found")
	}
	assertAtomicType(t, userNode, types.AtomicString)
}

func TestInfer_DynamicKeyPreservesNestedFields(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
	country := data.users[input.user].location.country
	country == "US"
}`)

	usersNode := si.Data.Properties["users"]
	if usersNode == nil {
		t.Fatal("data.users not found")
	}
	if usersNode.AdditionalProperties == nil {
		t.Fatal("data.users.AdditionalProperties is nil")
	}

	apNode := usersNode.AdditionalProperties
	assertKind(t, apNode, types.KindObject)

	locationNode := apNode.Properties["location"]
	if locationNode == nil {
		t.Fatal("data.users[*].location not found")
	}
	countryNode := locationNode.Properties["country"]
	if countryNode == nil {
		t.Fatal("data.users[*].location.country not found")
	}
	assertAtomicType(t, countryNode, types.AtomicString)
}

// ---- set membership (some x in coll / "val" in coll) -----------------------

func TestInfer_MembershipLiteralString(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { "admin" in data.users[input.user].roles }`)

	usersNode := si.Data.Properties["users"]
	if usersNode == nil || usersNode.AdditionalProperties == nil {
		t.Fatal("data.users dynamic node not found")
	}
	rolesNode := usersNode.AdditionalProperties.Properties["roles"]
	if rolesNode == nil {
		t.Fatal("data.users[*].roles not found")
	}
	assertKind(t, rolesNode, types.KindArray)
	if rolesNode.Items == nil {
		t.Fatal("data.users[*].roles.items is nil")
	}
	assertAtomicType(t, rolesNode.Items, types.AtomicString)
}

func TestInfer_MembershipLiteralInteger(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { 42 in data.scores }`)

	scoresNode := si.Data.Properties["scores"]
	if scoresNode == nil {
		t.Fatal("data.scores not found")
	}
	assertKind(t, scoresNode, types.KindArray)
	if scoresNode.Items == nil {
		t.Fatal("data.scores.items is nil")
	}
	assertAtomicType(t, scoresNode.Items, types.AtomicInt)
}

func TestInfer_SomeVarInCollection(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if { some role in data.roles; role == "admin" }`)

	rolesNode := si.Data.Properties["roles"]
	if rolesNode == nil {
		t.Fatal("data.roles not found")
	}
	assertKind(t, rolesNode, types.KindArray)
}

func TestInfer_SomeVarUsedAsDynamicKey(t *testing.T) {
	si := compileAndInfer(t, `package test
import rego.v1
allow if {
	"x" in data.strs
	some x in data.strs
	_ := data.lookup[x]
}`)

	strsNode := si.Data.Properties["strs"]
	if strsNode == nil {
		t.Fatal("data.strs not found")
	}
	if strsNode.Items == nil {
		t.Fatal("data.strs.items is nil")
	}
	assertAtomicType(t, strsNode.Items, types.AtomicString)

	lookupNode := si.Data.Properties["lookup"]
	if lookupNode == nil {
		t.Fatal("data.lookup not found")
	}
	assertKind(t, lookupNode, types.KindObject)
	if lookupNode.AdditionalProperties == nil {
		t.Error("data.lookup.AdditionalProperties is nil; expected dynamic-key object")
	}
}

// ---- RBAC policy full integration test --------------------------------------

const rbacPolicy = `package app.rbac
import rego.v1

default allow := false

allow if { user_is_admin }

allow if {
	some permission in user_is_granted
	input.action == permission.action
	input.type == permission.type
	country := data.users[input.user].location.country
	country == "US"
}

user_is_admin if {
	"admin" in data.users[input.user].roles
}

user_is_viewer if {
	"viewer" in data.users[input.user].roles
}

user_is_guest if {
	"guest" in data.users[input.user].roles
}

user_is_granted contains permission if {
	some role in data.users[input.user].roles
	some permission in data.role_permissions[role]
}`

func TestInfer_RBAC_InputUser_IsString(t *testing.T) {
	si := compileAndInfer(t, rbacPolicy)
	node := getNode(si.Input, "user")
	if node == nil {
		t.Fatal("input.user not found")
	}
	assertAtomicType(t, node, types.AtomicString)
}

func TestInfer_RBAC_InputActionAndType_Present(t *testing.T) {
	si := compileAndInfer(t, rbacPolicy)
	if getNode(si.Input, "action") == nil {
		t.Error("input.action not found in schema")
	}
	if getNode(si.Input, "type") == nil {
		t.Error("input.type not found in schema")
	}
}

func TestInfer_RBAC_DataUsers_IsDynamicObject(t *testing.T) {
	si := compileAndInfer(t, rbacPolicy)
	usersNode := si.Data.Properties["users"]
	if usersNode == nil {
		t.Fatal("data.users not found")
	}
	assertKind(t, usersNode, types.KindObject)
	if usersNode.AdditionalProperties == nil {
		t.Fatal("data.users.AdditionalProperties is nil; expected dynamic-key object")
	}
}

func TestInfer_RBAC_DataUsersRoles_ItemsAreString(t *testing.T) {
	si := compileAndInfer(t, rbacPolicy)
	usersNode := si.Data.Properties["users"]
	if usersNode == nil || usersNode.AdditionalProperties == nil {
		t.Fatal("data.users dynamic node not found")
	}
	apNode := usersNode.AdditionalProperties
	rolesNode := apNode.Properties["roles"]
	if rolesNode == nil {
		t.Fatal("data.users[*].roles not found")
	}
	assertKind(t, rolesNode, types.KindArray)
	if rolesNode.Items == nil {
		t.Fatal("data.users[*].roles.items is nil")
	}
	assertAtomicType(t, rolesNode.Items, types.AtomicString)
}

func TestInfer_RBAC_DataUsersLocationCountry_IsString(t *testing.T) {
	si := compileAndInfer(t, rbacPolicy)
	usersNode := si.Data.Properties["users"]
	if usersNode == nil || usersNode.AdditionalProperties == nil {
		t.Fatal("data.users dynamic node not found")
	}
	apNode := usersNode.AdditionalProperties
	locationNode := apNode.Properties["location"]
	if locationNode == nil {
		t.Fatal("data.users[*].location not found")
	}
	countryNode := locationNode.Properties["country"]
	if countryNode == nil {
		t.Fatal("data.users[*].location.country not found")
	}
	assertAtomicType(t, countryNode, types.AtomicString)
}

func TestInfer_RBAC_DataRolePermissions_IsDynamicObject(t *testing.T) {
	si := compileAndInfer(t, rbacPolicy)
	rpNode := si.Data.Properties["role_permissions"]
	if rpNode == nil {
		t.Fatal("data.role_permissions not found")
	}
	assertKind(t, rpNode, types.KindObject)
	if rpNode.AdditionalProperties == nil {
		t.Fatal("data.role_permissions.AdditionalProperties is nil; expected dynamic-key object")
	}
	assertKind(t, rpNode.AdditionalProperties, types.KindArray)
}
