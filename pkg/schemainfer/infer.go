// Package schemainfer derives an input/data JSON Schema from a compiled Rego module
// by walking the AST and collecting type constraints on input.* and data.* references.
//
// The inferred schema is a best-effort approximation: it captures types that can be
// determined statically from literal comparisons, equality constraints, and builtin
// function usage. References that appear only in opaque contexts remain typed as
// "unknown" (represented as an empty JSON Schema object).
package schemainfer

import (
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

// SchemaNode is one node in the inferred schema tree.
//
// Leaf nodes carry a Hint (the inferred RegoTypeDef for this position).
// Intermediate nodes with Properties are implicitly objects; with Items,
// implicitly arrays; with AdditionalProperties, dynamic-key objects.
// When Hint.Kind is KindUnknown and structural fields are populated,
// effectiveType() derives the kind from the structure.
type SchemaNode struct {
	Hint                 types.RegoTypeDef
	Properties           map[string]*SchemaNode // non-nil iff object fields were observed
	Items                *SchemaNode            // non-nil iff array iteration was observed
	AdditionalProperties *SchemaNode            // non-nil iff dynamic key access was observed
}

func newNode() *SchemaNode {
	return &SchemaNode{Hint: types.NewUnknownType()}
}

// mergeType returns incoming if existing is unknown, otherwise existing.
// This implements "first concrete type wins" semantics for incremental inference.
func mergeType(existing, incoming types.RegoTypeDef) types.RegoTypeDef {
	if existing.IsUnknown() {
		return incoming
	}
	return existing
}

// effectiveType resolves the best type for a node, taking structural evidence
// (presence of Properties, AdditionalProperties, or Items) into account when
// the explicit Hint is unknown.
func effectiveType(node *SchemaNode) types.RegoTypeDef {
	if !node.Hint.IsUnknown() {
		return node.Hint
	}
	if len(node.Properties) > 0 || node.AdditionalProperties != nil {
		return types.RegoTypeDef{Kind: types.KindObject}
	}
	if node.Items != nil {
		return types.RegoTypeDef{Kind: types.KindArray}
	}
	return types.NewUnknownType()
}

// SchemaInferrer walks a compiled Rego module and builds schema trees for
// the input document and the data document.
type SchemaInferrer struct {
	// Input is the schema tree inferred for input.*
	Input *SchemaNode
	// Data is the schema tree inferred for data.* (external data only;
	// refs under the module's own package path are skipped).
	Data *SchemaNode

	// packagePrefix is set to the module's package path string so that
	// references to the module's own rules are not treated as external data.
	packagePrefix string

	// varBindings maps local variable names (e.g. "__local0__") to the input/data
	// ref term they were bound to within the current rule body.
	// OPA's compiler introduces temp vars for sub-expressions:
	//   input.user.age > 18  →  eq(__local0__, input.user.age); gt(__local0__, 18)
	// Tracking these lets us propagate type hints back to the original ref.
	varBindings map[string]*ast.Term

	// varElemHints maps a variable name to the RegoTypeDef of the collection elements
	// it represents, set when handling `some x in coll` membership patterns.
	// This allows us to recognise when a variable used as an object key (e.g.
	// data.role_permissions[role]) came from iterating a string-typed collection,
	// and therefore treat the parent as a dynamic-key object rather than an array.
	varElemHints map[string]types.RegoTypeDef
}

// New creates a fresh SchemaInferrer.
func New() *SchemaInferrer {
	return &SchemaInferrer{
		Input:        newNode(),
		Data:         newNode(),
		varElemHints: make(map[string]types.RegoTypeDef),
	}
}

// InferFromModule walks all rules in mod and records type constraints.
// packagePath should be the compiled module's package path (e.g. "data.example.authz")
// so that intra-package rule references are excluded from the data schema.
func (si *SchemaInferrer) InferFromModule(mod *ast.Module, packagePath ast.Ref) {
	if packagePath != nil {
		si.packagePrefix = packagePath.String() + "."
	}
	for _, rule := range mod.Rules {
		si.walkRule(rule)
	}
}

func (si *SchemaInferrer) walkRule(rule *ast.Rule) {
	// Each rule body gets its own variable-binding scope.
	si.varBindings = make(map[string]*ast.Term)
	si.varElemHints = make(map[string]types.RegoTypeDef)
	for _, expr := range rule.Body {
		si.walkExpr(expr)
	}
	if rule.Else != nil {
		si.walkRule(rule.Else)
	}
}

func (si *SchemaInferrer) walkExpr(expr *ast.Expr) {
	if expr == nil {
		return
	}

	// Non-call expression: single term (e.g. `input.active`)
	if !expr.IsCall() {
		if term, ok := expr.Terms.(*ast.Term); ok {
			si.recordRef(term, types.NewUnknownType())
		}
		return
	}

	terms, ok := expr.Terms.([]*ast.Term)
	if !ok || len(terms) == 0 {
		return
	}

	op := terms[0].String()
	args := terms[1:]

	switch {
	case types.IsEqualityOp(op) && len(args) == 2:
		si.handleEquality(args[0], args[1])

	case types.IsNumericCompOp(op):
		intType := types.NewAtomicType(types.AtomicInt)
		for _, arg := range args {
			si.recordRef(arg, intType)
		}

	// `x in coll` membership check compiles to internal.member_2(elem, coll).
	case op == "internal.member_2" && len(args) == 2:
		si.handleMembership(args[0], args[1])

	// 3-arg form internal.member_2(elem, idx, coll) appears in some OPA versions.
	case op == "internal.member_2" && len(args) == 3:
		si.handleMembership(args[0], args[2])

	// `some k, v in obj` compiles to internal.member_3(key, val, coll).
	case op == "internal.member_3" && len(args) == 3:
		si.recordRef(args[2], types.RegoTypeDef{Kind: types.KindObject})

	// `x in coll` (without some) may also compile to member(x, coll).
	case op == "member" && len(args) == 2:
		si.handleMembership(args[0], args[1])

	default:
		hints := builtinParamHints(op, len(args))
		for i, arg := range args {
			hint := types.NewUnknownType()
			if i < len(hints) {
				hint = hints[i]
			}
			si.recordRef(arg, hint)
		}
	}
}

// handleEquality infers types for both sides of an equality/assignment expression.
// When one side is a literal and the other is an input/data ref, the ref gets the
// literal's type. Local variables bound to input/data refs are recorded in
// varBindings so that subsequent expressions can propagate type hints back.
func (si *SchemaInferrer) handleEquality(left, right *ast.Term) {
	leftHint := types.LiteralTermType(left)
	rightHint := types.LiteralTermType(right)

	// Record variable → ref bindings so later expressions can propagate hints.
	si.tryRecordVarBinding(left, right)
	si.tryRecordVarBinding(right, left)

	// Propagate the known side's hint to the ref on the other side.
	si.recordRef(left, rightHint)
	si.recordRef(right, leftHint)
}

// handleMembership processes `elem in coll` patterns.
// It marks the collection as an array/set, propagates the element's literal type
// to the collection's items, and records the element variable's type hint so it
// can later be recognised as a dynamic object key (e.g. data.x[role]).
func (si *SchemaInferrer) handleMembership(elem, coll *ast.Term) {
	// Mark the collection as an array/set.
	si.recordRef(coll, types.RegoTypeDef{Kind: types.KindArray})

	// If the element is a literal, propagate its type to the collection's items.
	elemHint := types.LiteralTermType(elem)
	if !elemHint.IsUnknown() {
		si.setCollectionItemsHint(coll, elemHint)
	}

	// Bind the element variable to the items type for later use as a dynamic key.
	if v, ok := elem.Value.(ast.Var); ok {
		varName := string(v)
		finalHint := elemHint
		if finalHint.IsUnknown() {
			// Check if the collection already has a known items type.
			if node := si.navigateToNode(coll); node != nil && node.Items != nil {
				finalHint = node.Items.Hint
			}
		}
		if !finalHint.IsUnknown() {
			si.varElemHints[varName] = finalHint
		}
	}
}

// setCollectionItemsHint navigates to the node for coll and sets its Items hint.
func (si *SchemaInferrer) setCollectionItemsHint(coll *ast.Term, hint types.RegoTypeDef) {
	if hint.IsUnknown() {
		return
	}
	node := si.navigateToNode(coll)
	if node == nil {
		return
	}
	if node.Items == nil {
		node.Items = newNode()
	}
	node.Items.Hint = mergeType(node.Items.Hint, hint)
}

// navigateToNode walks the schema tree following the path described by term
// (which must be an input.* or data.* ref) and returns the leaf SchemaNode,
// or nil if the path does not yet exist in the tree.
// Unlike recordRef it does not create nodes — it is purely read-only.
func (si *SchemaInferrer) navigateToNode(term *ast.Term) *SchemaNode {
	if term == nil {
		return nil
	}
	// Follow variable bindings.
	if v, ok := term.Value.(ast.Var); ok {
		if bound, exists := si.varBindings[string(v)]; exists {
			return si.navigateToNode(bound)
		}
		return nil
	}
	ref, ok := term.Value.(ast.Ref)
	if !ok || len(ref) == 0 {
		return nil
	}
	prefix := ref[0].String()
	var root *SchemaNode
	switch prefix {
	case "input":
		root = si.Input
	case "data":
		if si.packagePrefix != "" && strings.HasPrefix(ref.String(), si.packagePrefix) {
			return nil
		}
		root = si.Data
	default:
		return nil
	}
	current := root
	for i := 1; i < len(ref); i++ {
		seg := ref[i]
		key, isGround := segmentKey(seg)
		if !isGround {
			if si.isDynamicKey(seg) {
				if current.AdditionalProperties == nil {
					return nil
				}
				current = current.AdditionalProperties
			} else {
				if current.Items == nil {
					return nil
				}
				current = current.Items
			}
			continue
		}
		if current.Properties == nil {
			return nil
		}
		child, exists := current.Properties[key]
		if !exists {
			return nil
		}
		current = child
	}
	return current
}

// tryRecordVarBinding records a binding varTerm → refTerm when varTerm is a
// local variable and refTerm is an input.* or data.* reference.
func (si *SchemaInferrer) tryRecordVarBinding(varTerm, refTerm *ast.Term) {
	if varTerm == nil || refTerm == nil {
		return
	}
	v, ok := varTerm.Value.(ast.Var)
	if !ok {
		return
	}
	ref, ok := refTerm.Value.(ast.Ref)
	if !ok || len(ref) == 0 {
		return
	}
	prefix := ref[0].String()
	if prefix != "input" && prefix != "data" {
		return
	}
	si.varBindings[string(v)] = refTerm
}

// isDynamicKey reports whether a reference segment represents a dynamic object
// key rather than an array index. This is true when:
//   - the segment is a Var bound (via varBindings) to an input.* or data.* ref,
//   - the segment is a Var known to have string type (from set-membership inference), or
//   - the segment is itself a Ref starting with input.* or data.*.
func (si *SchemaInferrer) isDynamicKey(seg *ast.Term) bool {
	switch v := seg.Value.(type) {
	case ast.Var:
		varName := string(v)
		if _, bound := si.varBindings[varName]; bound {
			return true
		}
		h := si.varElemHints[varName]
		return h.Kind == types.KindAtomic && h.AtomicType == types.AtomicString
	case ast.Ref:
		prefix := v[0].String()
		return prefix == "input" || prefix == "data"
	default:
		return false
	}
}

// recordRef checks whether term is an input.* or data.* reference (or a local
// variable bound to one) and adds it to the schema tree with the given hint.
func (si *SchemaInferrer) recordRef(term *ast.Term, hint types.RegoTypeDef) {
	if term == nil {
		return
	}

	// If the term is a local variable bound to an input/data ref, follow it.
	if v, ok := term.Value.(ast.Var); ok {
		if bound, exists := si.varBindings[string(v)]; exists {
			si.recordRef(bound, hint)
		}
		return
	}

	ref, ok := term.Value.(ast.Ref)
	if !ok || len(ref) == 0 {
		return
	}

	prefix := ref[0].String()
	var root *SchemaNode
	switch prefix {
	case "input":
		root = si.Input
	case "data":
		// Skip self-referential rule lookups (e.g. data.pkg.rule)
		if si.packagePrefix != "" && strings.HasPrefix(ref.String(), si.packagePrefix) {
			return
		}
		root = si.Data
	default:
		return
	}

	// Walk the reference path, creating/updating nodes as we go.
	current := root
	for i := 1; i < len(ref); i++ {
		seg := ref[i]
		key, isGround := segmentKey(seg)

		if !isGround {
			if si.isDynamicKey(seg) {
				// Dynamic object key (e.g. data.users[input.user] or data.x[role]).
				// Infer the key itself as string since object keys are strings.
				current.Hint = mergeType(current.Hint, types.RegoTypeDef{Kind: types.KindObject})
				si.recordRef(seg, types.NewAtomicType(types.AtomicString))
				if current.AdditionalProperties == nil {
					current.AdditionalProperties = newNode()
				}
				current = current.AdditionalProperties
			} else {
				// Non-ground variable = array/set iteration (e.g. input.items[_]).
				current.Hint = mergeType(current.Hint, types.RegoTypeDef{Kind: types.KindArray})
				if current.Items == nil {
					current.Items = newNode()
				}
				current = current.Items
			}
			continue
		}

		// Ground string key = object field access.
		_ = key
		current.Hint = mergeType(current.Hint, types.RegoTypeDef{Kind: types.KindObject})
		if current.Properties == nil {
			current.Properties = make(map[string]*SchemaNode)
		}
		if _, exists := current.Properties[key]; !exists {
			current.Properties[key] = newNode()
		}
		current = current.Properties[key]
	}

	// Apply the inferred type hint to the leaf.
	if !hint.IsUnknown() {
		current.Hint = mergeType(current.Hint, hint)
	}
}

// segmentKey extracts the string key from a reference segment and reports
// whether the segment is ground (i.e. a constant string key, not a variable).
func segmentKey(term *ast.Term) (key string, isGround bool) {
	switch v := term.Value.(type) {
	case ast.String:
		return string(v), true
	case ast.Var:
		// Variables used as indices are non-ground (iteration).
		return string(v), false
	default:
		return term.String(), term.Value.IsGround()
	}
}

// builtinParamHints returns per-argument type hints for known OPA builtins by
// consulting the predefined-function registry from pkg/types. The returned
// slice has length equal to arity; positions whose type cannot be determined
// hold NewUnknownType().
func builtinParamHints(op string, arity int) []types.RegoTypeDef {
	hints := make([]types.RegoTypeDef, arity)
	for i := range hints {
		hints[i] = types.NewUnknownType()
	}
	pf, ok := types.GetPredefFunctions()[op]
	if !ok {
		return hints
	}
	if pf.CheckArity != nil && !pf.CheckArity(arity) {
		return hints
	}
	if pf.UpdateParams == nil {
		return hints
	}
	pf.UpdateParams(hints)
	return hints
}
