package types

import (
	"github.com/open-policy-agent/opa/v1/ast"
)

// VarKind classifies a variable's role within a compiled Rego rule body.
type VarKind string

const (
	// VarKindLocal represents variables bound via assignment (:= or =).
	VarKindLocal VarKind = "local"

	// VarKindQuantified represents variables that are not bound by assignment
	// (iteration indices, free variables in comparisons, head keys, etc.).
	VarKindQuantified VarKind = "quantified"
)

// VarClassification holds the local vs. quantified classification of every
// variable encountered in a compiled Rego rule body.
//
// A variable appears in at most one of the two sets.  The anonymous wildcard
// "_" and the top-level namespace roots "data"/"input"/"rego" are excluded
// from both sets.
type VarClassification struct {
	// Local contains variable names that are the LHS of an assignment (= or :=).
	Local map[string]bool
	// Quantified contains all other variable names (ref indices, free vars, …).
	Quantified map[string]bool
}

// IsLocal reports whether the named variable is classified as local.
func (vc *VarClassification) IsLocal(name string) bool { return vc.Local[name] }

// IsQuantified reports whether the named variable is classified as quantified.
func (vc *VarClassification) IsQuantified(name string) bool { return vc.Quantified[name] }

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
// classifies each variable as local or quantified.
//
// A variable is local if and only if it appears as the LHS of an assignment
// expression (Rego := or =, compiled to "assign" or "unify").  All other
// variable occurrences are quantified.  If a variable is already classified
// as quantified (e.g. it is the head key of a partial rule), a subsequent
// assignment in the body does not demote it to local.
//
// The wildcard "_" and namespace roots "data", "input", "rego" are excluded
// from both sets.
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
	// Head key of a partial-set / partial-object rule is always quantified.
	if rule.Head.Key != nil {
		collectVarsQuantified(rule.Head.Key, vc)
	}
	for _, expr := range rule.Body {
		classifyExpr(expr, vc)
	}
	if rule.Else != nil {
		classifyRule(rule.Else, vc)
	}
}

// classifyExpr classifies the variables within a single expression.
//
// For equality/assignment calls (eq/assign/unify with 2 args) the LHS variable
// is marked local; for every other expression all variable occurrences are
// quantified.
func classifyExpr(expr *ast.Expr, vc *VarClassification) {
	switch terms := expr.Terms.(type) {
	case *ast.Term:
		collectVarsQuantified(terms, vc)
	case []*ast.Term:
		if expr.IsCall() && len(terms) > 0 {
			op, args := terms[0].String(), terms[1:]
			if IsEqualityOp(op) && len(args) == 2 {
				markLocalIfVar(args[0], vc)        // LHS is the assigned variable → local
				collectVarsQuantified(args[1], vc) // RHS vars are quantified
			} else {
				for _, arg := range args {
					collectVarsQuantified(arg, vc)
				}
			}
		} else {
			for _, t := range terms {
				collectVarsQuantified(t, vc)
			}
		}
	}
	for _, w := range expr.With {
		collectVarsQuantified(w.Value, vc)
	}
}

// markLocalIfVar marks a term's variable as local, provided it has not already
// been classified as quantified.  Excluded names are silently ignored.
func markLocalIfVar(term *ast.Term, vc *VarClassification) {
	if v, ok := term.Value.(ast.Var); ok {
		name := string(v)
		if !isExcluded(name) && !vc.Quantified[name] {
			vc.Local[name] = true
		}
	}
}

// collectVarsQuantified recursively walks term and marks every variable it
// finds as quantified, unless the variable is already classified as local.
func collectVarsQuantified(term *ast.Term, vc *VarClassification) {
	if term == nil {
		return
	}
	switch v := term.Value.(type) {
	case ast.Var:
		name := string(v)
		if !isExcluded(name) && !vc.Local[name] {
			vc.Quantified[name] = true
		}
	case ast.Ref:
		for _, seg := range v {
			collectVarsQuantified(seg, vc)
		}
	case *ast.Array:
		for i := 0; i < v.Len(); i++ {
			collectVarsQuantified(v.Elem(i), vc)
		}
	case ast.Object:
		v.Foreach(func(k, val *ast.Term) {
			collectVarsQuantified(k, vc)
			collectVarsQuantified(val, vc)
		})
	case ast.Set:
		v.Foreach(func(elem *ast.Term) {
			collectVarsQuantified(elem, vc)
		})
	case ast.Call:
		for _, t := range v {
			collectVarsQuantified(t, vc)
		}
	}
}
