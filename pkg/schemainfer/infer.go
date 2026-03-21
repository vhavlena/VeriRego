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

// TypeHint represents a coarsely inferred type for a schema path.
type TypeHint int

const (
	HintUnknown TypeHint = iota
	HintString
	HintInteger
	HintBoolean
	HintObject
	HintArray
	HintNull
)

// SchemaNode is one node in the inferred schema tree.
// A leaf node with no Properties/Items carries only a TypeHint.
// An intermediate node with Properties is implicitly an object.
// A node with Items is implicitly an array.
type SchemaNode struct {
	Hint       TypeHint
	Properties map[string]*SchemaNode // non-nil iff object fields were observed
	Items      *SchemaNode            // non-nil iff array iteration was observed
}

func newNode() *SchemaNode {
	return &SchemaNode{Hint: HintUnknown}
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
}

// New creates a fresh SchemaInferrer.
func New() *SchemaInferrer {
	return &SchemaInferrer{
		Input: newNode(),
		Data:  newNode(),
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
			si.recordRef(term, HintUnknown)
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
	case isEqualityOp(op) && len(args) == 2:
		si.handleEquality(args[0], args[1])

	case isNumericCompOp(op):
		for _, arg := range args {
			si.recordRef(arg, HintInteger)
		}

	default:
		hints := builtinParamHints(op, len(args))
		for i, arg := range args {
			hint := HintUnknown
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
	leftHint := literalHint(left)
	rightHint := literalHint(right)

	// Record variable → ref bindings so later expressions can propagate hints.
	// Pattern: eq(var, input.x) or eq(input.x, var)
	si.tryRecordVarBinding(left, right)
	si.tryRecordVarBinding(right, left)

	// Propagate the known side's hint to the ref on the other side.
	si.recordRef(left, rightHint)
	si.recordRef(right, leftHint)
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

// recordRef checks whether term is an input.* or data.* reference (or a local
// variable bound to one) and adds it to the schema tree with the given hint.
func (si *SchemaInferrer) recordRef(term *ast.Term, hint TypeHint) {
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
			// Non-ground segment = iteration over an array (e.g. input.items[_])
			current.Hint = mergeHint(current.Hint, HintArray)
			if current.Items == nil {
				current.Items = newNode()
			}
			current = current.Items
			continue
		}

		// Ground string key = object field access
		current.Hint = mergeHint(current.Hint, HintObject)
		if current.Properties == nil {
			current.Properties = make(map[string]*SchemaNode)
		}
		if _, exists := current.Properties[key]; !exists {
			current.Properties[key] = newNode()
		}
		current = current.Properties[key]
	}

	// Apply the inferred type hint to the leaf.
	if hint != HintUnknown {
		current.Hint = mergeHint(current.Hint, hint)
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

// mergeHint combines an existing hint with a new one.
// Unknown is the bottom element; any concrete type takes precedence.
// If two different concrete types conflict, the existing one is kept.
func mergeHint(existing, incoming TypeHint) TypeHint {
	if existing == HintUnknown {
		return incoming
	}
	return existing
}

// literalHint returns the TypeHint for a literal term, or HintUnknown for non-literals.
func literalHint(term *ast.Term) TypeHint {
	if term == nil {
		return HintUnknown
	}
	switch term.Value.(type) {
	case ast.String:
		return HintString
	case ast.Number:
		return HintInteger
	case ast.Boolean:
		return HintBoolean
	case ast.Null:
		return HintNull
	case *ast.Array:
		return HintArray
	case ast.Object:
		return HintObject
	default:
		return HintUnknown
	}
}

// isEqualityOp reports whether op is an OPA equality/assignment operator.
func isEqualityOp(op string) bool {
	switch op {
	case "eq", "assign", "unify":
		return true
	}
	return false
}

// isNumericCompOp reports whether op is a numeric comparison operator.
func isNumericCompOp(op string) bool {
	switch op {
	case "gt", "lt", "gte", "lte":
		return true
	}
	return false
}

// builtinParamHints returns per-argument type hints for known OPA builtins by
// consulting the predefined-function registry from pkg/types. The returned
// slice has length equal to arity; positions whose type cannot be determined
// hold HintUnknown.
func builtinParamHints(op string, arity int) []TypeHint {
	hints := make([]TypeHint, arity)
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
	pars := make([]types.RegoTypeDef, arity)
	for i := range pars {
		pars[i] = types.NewUnknownType()
	}
	pf.UpdateParams(pars)
	for i, p := range pars {
		hints[i] = regoTypeToHint(p)
	}
	return hints
}

// regoTypeToHint converts a RegoTypeDef (from the types package) to a TypeHint.
func regoTypeToHint(t types.RegoTypeDef) TypeHint {
	switch t.Kind {
	case types.KindAtomic:
		switch t.AtomicType {
		case types.AtomicString:
			return HintString
		case types.AtomicInt:
			return HintInteger
		case types.AtomicBoolean:
			return HintBoolean
		case types.AtomicNull:
			return HintNull
		}
	case types.KindArray:
		return HintArray
	case types.KindObject:
		return HintObject
	}
	return HintUnknown
}
