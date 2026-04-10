package types

import (
	"github.com/open-policy-agent/opa/v1/ast"
)

// VarKind classifies a variable's role within a compiled Rego rule body.
type VarKind string

const (
	// VarKindLocal represents variables that hold intermediate or assigned values,
	// including OPA-compiler-generated __localN__ temporaries and user-defined
	// variables bound via equality to a concrete value.
	VarKindLocal VarKind = "local"

	// VarKindQuantified represents variables that act as iteration indices or
	// collection element values.  After OPA compilation this covers:
	//   • non-ground (variable) indices inside a ref: coll[x]
	//   • the LHS of an equality whose RHS is a ref with a variable index:
	//       val = coll[x]  ← val is the iterated value, x is the iterated key
	//   • arguments to internal.member_2 / internal.member_3 membership builtins
	//     (emitted by OPA for "some x in coll" patterns in some compiler versions)
	//   • the head key of a partial-set / partial-object rule
	VarKindQuantified VarKind = "quantified"
)

// VarClassification holds the local vs. quantified classification of every
// variable encountered in a compiled Rego rule body.
//
// A variable appears in at most one of the two sets.  The anonymous wildcard
// "_" and the top-level namespace roots "data"/"input" are excluded from
// both sets.
type VarClassification struct {
	// Local contains variable names that are assigned intermediate values.
	Local map[string]bool
	// Quantified contains variable names that act as iteration indices or
	// collection element values.
	Quantified map[string]bool
}

// IsLocal reports whether the named variable is classified as local.
func (vc *VarClassification) IsLocal(name string) bool {
	return vc.Local[name]
}

// IsQuantified reports whether the named variable is classified as quantified.
func (vc *VarClassification) IsQuantified(name string) bool {
	return vc.Quantified[name]
}

// isExcluded reports whether a variable name should be excluded from
// classification entirely (wildcard, top-level namespace roots).
func isExcluded(name string) bool {
	switch name {
	case "_", "data", "input", "rego":
		return true
	}
	return false
}

// ClassifyVars analyzes a compiled Rego rule (including else branches) and
// classifies each variable in its body as either quantified or local.
//
// The rule must already have been processed by OPA's compiler so that
// compiler-generated temporaries (__local0__, __local1__, …) are present.
//
// Classification rules:
//
//	Quantified — a variable is quantified when it appears as:
//	  • a non-ground (variable) index at position ≥ 1 inside a ref: coll[x]
//	  • the LHS of an equality whose RHS is a ref containing a variable
//	    index — this captures the compiled form of "some v in coll" which
//	    OPA translates to  val = coll[idx]  (val is the iterated value)
//	  • the element / key / value argument of internal.member_2 or
//	    internal.member_3 membership builtins (older compiler versions)
//	  • the head key of a partial-set / partial-object rule: rule[key] { … }
//
//	Local — all other variables encountered in the rule body that are not
//	already classified as quantified.
//
// If a variable matches both patterns (e.g. used as a ref index and also in an
// equality), the quantified classification takes precedence.
//
// The anonymous wildcard "_" and the top-level roots "data", "input", "rego"
// are excluded from both sets.
func ClassifyVars(rule *ast.Rule) VarClassification {
	vc := VarClassification{
		Local:      make(map[string]bool),
		Quantified: make(map[string]bool),
	}
	classifyRule(rule, &vc)
	return vc
}

// classifyRule processes a rule (and any else branch) into vc.
func classifyRule(rule *ast.Rule, vc *VarClassification) {
	// Head key of a partial-set / partial-object rule is quantified.
	// e.g.  rule[key] { ... }  →  key generates values for the set/object.
	if rule.Head.Key != nil {
		markQuantifiedIfVar(rule.Head.Key, vc)
	}

	classifyBody(rule.Body, vc)

	if rule.Else != nil {
		classifyRule(rule.Else, vc)
	}
}

// classifyBody walks every expression in a rule body and updates vc.
func classifyBody(body ast.Body, vc *VarClassification) {
	for _, expr := range body {
		classifyExpr(expr, vc)
	}
}

// classifyExpr classifies the variables within a single expression.
func classifyExpr(expr *ast.Expr, vc *VarClassification) {
	switch terms := expr.Terms.(type) {
	case *ast.Term:
		// Single-term expression (e.g. a bare ref used as a boolean test).
		collectVarsFromTerm(terms, vc)

	case []*ast.Term:
		if len(terms) == 0 {
			return
		}
		if !expr.IsCall() {
			for _, t := range terms {
				collectVarsFromTerm(t, vc)
			}
			break
		}

		op := terms[0].String()
		args := terms[1:]
		classifyCall(op, args, vc)
	}

	// Traverse "with" modifier values (e.g. `f(x) with input.user as x`).
	// Variables that appear only in with-value positions must also be classified.
	for _, w := range expr.With {
		collectVarsFromTerm(w.Value, vc)
	}
}

// classifyCall applies classification rules for a call expression.
func classifyCall(op string, args []*ast.Term, vc *VarClassification) {
	switch {
	// Equality / assignment / unification operators.
	// The LHS always receives a value and is classified as local, regardless of
	// whether the RHS is a collection access.  Non-ground index variables inside
	// the RHS ref (e.g. coll[idx]) are classified as quantified by
	// collectVarsFromTerm when it descends into the ref.
	//
	// Example:  __local2__ = data.valid[__local1__]
	//   __local1__ → quantified  (ref index, detected inside collectVarsFromTerm)
	//   __local2__ → local       (LHS receives the fetched value)
	case IsEqualityOp(op) && len(args) == 2:
		lhs, rhs := args[0], args[1]
		collectVarsFromTerm(lhs, vc)
		collectVarsFromTerm(rhs, vc)

	// internal.member_2(elem, coll)  — 2-arg membership (some x in coll).
	case op == "internal.member_2" && len(args) == 2:
		markQuantifiedIfVar(args[0], vc)
		collectVarsFromTerm(args[1], vc)

	// internal.member_2(key, val, coll)  — 3-arg form.
	case op == "internal.member_2" && len(args) == 3:
		collectVarsFromTerm(args[0], vc)
		markQuantifiedIfVar(args[1], vc)
		collectVarsFromTerm(args[2], vc)

	// internal.member_3(k, v, coll)  — some k, v in coll.
	case op == "internal.member_3" && len(args) == 3:
		markQuantifiedIfVar(args[0], vc)
		markQuantifiedIfVar(args[1], vc)
		collectVarsFromTerm(args[2], vc)

	default:
		for _, arg := range args {
			collectVarsFromTerm(arg, vc)
		}
	}
}

// markQuantifiedIfVar marks a term's variable as quantified (and removes it
// from the local set if it was added there earlier).  Excluded names are
// silently ignored.
func markQuantifiedIfVar(term *ast.Term, vc *VarClassification) {
	if v, ok := term.Value.(ast.Var); ok {
		name := string(v)
		if isExcluded(name) {
			return
		}
		vc.Quantified[name] = true
		delete(vc.Local, name)
	}
}

// collectVarsFromTerm recursively walks a term and adds every variable it finds
// to vc.Local (unless it is already in vc.Quantified or is excluded).
// Non-ground (variable) indices inside refs are detected here and classified as
// quantified.
func collectVarsFromTerm(term *ast.Term, vc *VarClassification) {
	if term == nil {
		return
	}

	switch v := term.Value.(type) {
	case ast.Var:
		name := string(v)
		if isExcluded(name) {
			return
		}
		if !vc.Quantified[name] {
			vc.Local[name] = true
		}

	case ast.Ref:
		// ref[0] is the base (e.g. "data", "input", or a named variable).
		// We skip it for namespace roots; for user variables it is classified
		// as local (it's being indexed into, not assigned).
		if len(v) > 0 {
			collectVarsFromTerm(v[0], vc)
		}
		// ref[1:] are the path segments; a variable at any of these positions
		// is a non-ground index and therefore quantified.
		for i := 1; i < len(v); i++ {
			if _, isVar := v[i].Value.(ast.Var); isVar {
				markQuantifiedIfVar(v[i], vc)
			} else {
				collectVarsFromTerm(v[i], vc)
			}
		}

	case *ast.Array:
		for i := 0; i < v.Len(); i++ {
			collectVarsFromTerm(v.Elem(i), vc)
		}

	case ast.Object:
		v.Foreach(func(k, val *ast.Term) {
			collectVarsFromTerm(k, vc)
			collectVarsFromTerm(val, vc)
		})

	case ast.Set:
		v.Foreach(func(elem *ast.Term) {
			collectVarsFromTerm(elem, vc)
		})

	case ast.Call:
		for _, t := range v {
			collectVarsFromTerm(t, vc)
		}
	}
}
