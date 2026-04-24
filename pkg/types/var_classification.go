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

	// VarKindParameter represents variables declared as rule or function
	// parameters in the rule head (rule.Head.Args).
	VarKindParameter VarKind = "parameter"
)

// VarClassification holds the local / quantified / parameter classification of
// every variable encountered in a compiled Rego rule body.
//
// A variable appears in at most one of the three sets.  The anonymous wildcard
// "_" and the top-level namespace roots "data"/"input"/"rego" are excluded
// from all sets.
type VarClassification struct {
	// Local contains variable names that are the LHS of an assignment (= or :=).
	Local map[string]bool
	// Quantified contains all other variable names (ref indices, free vars, …).
	Quantified map[string]bool
	// Parameter contains variable names declared as rule/function parameters in
	// the rule head (rule.Head.Args).  Parameters are excluded from both Local
	// and Quantified.
	Parameter map[string]bool
}

// IsLocal reports whether the named variable is classified as local.
func (vc *VarClassification) IsLocal(name string) bool { return vc.Local[name] }

// IsQuantified reports whether the named variable is classified as quantified.
func (vc *VarClassification) IsQuantified(name string) bool { return vc.Quantified[name] }

// IsParameter reports whether the named variable is a rule/function parameter.
func (vc *VarClassification) IsParameter(name string) bool { return vc.Parameter[name] }

// Merge adds all entries from other into vc.
func (vc *VarClassification) Merge(other VarClassification) {
	for k, v := range other.Local {
		vc.Local[k] = v
	}
	for k, v := range other.Quantified {
		vc.Quantified[k] = v
	}
	for k, v := range other.Parameter {
		vc.Parameter[k] = v
	}
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


// collectVars walks term recursively, calling onVar for every non-excluded variable name.
func collectVars(term *ast.Term, onVar func(string)) {
	if term == nil {
		return
	}
	switch v := term.Value.(type) {
	case ast.Var:
		if name := string(v); !isExcluded(name) {
			onVar(name)
		}
	case ast.Ref:
		for _, seg := range v {
			collectVars(seg, onVar)
		}
	case *ast.Array:
		for i := 0; i < v.Len(); i++ {
			collectVars(v.Elem(i), onVar)
		}
	case ast.Object:
		v.Foreach(func(k, val *ast.Term) {
			collectVars(k, onVar)
			collectVars(val, onVar)
		})
	case ast.Set:
		v.Foreach(func(elem *ast.Term) { collectVars(elem, onVar) })
	case ast.Call:
		for _, t := range v {
			collectVars(t, onVar)
		}
	}
}

// collectVarsLocal marks every variable in term as local, unless already quantified/parameter.
func collectVarsLocal(term *ast.Term, vc *VarClassification) {
	collectVars(term, func(name string) {
		if !vc.Quantified[name] && !vc.Parameter[name] {
			vc.Local[name] = true
		}
	})
}

// ClassifyVarsBranch classifies variables for a single rule branch (the head
// and body of rule only — else branches are NOT traversed).  Variables
// appearing in the rule head value are additionally marked as local, because
// they are output variables scoped to this branch.
//
// Rule/function parameters (rule.Head.Args) are placed in the Parameter set
// and excluded from both Local and Quantified.
//
// Use this instead of [ClassifyVars] when processing each else branch as an
// independent scope.
func ClassifyVarsBranch(rule *ast.Rule) VarClassification {
	vc := VarClassification{
		Local:      make(map[string]bool),
		Quantified: make(map[string]bool),
		Parameter:  make(map[string]bool),
	}
	// Seed parameters so they are excluded from Local and Quantified.
	for _, arg := range rule.Head.Args {
		if v, ok := arg.Value.(ast.Var); ok {
			vc.Parameter[string(v)] = true
		}
	}
	// Variables in the head value act as outputs of this branch — treat as local.
	if rule.Head.Value != nil {
		collectVarsLocal(rule.Head.Value, &vc)
	}
	// Head key of a partial-set / partial-object rule is quantified.
	if rule.Head.Key != nil {
		collectVarsQuantified(rule.Head.Key, &vc)
	}
	// Classify body expressions (no else recursion).
	for _, expr := range rule.Body {
		classifyExpr(expr, &vc)
	}
	return vc
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
		Parameter:  make(map[string]bool),
	}
	// Seed parameters from the top-level rule head; else branches share them.
	for _, arg := range rule.Head.Args {
		if v, ok := arg.Value.(ast.Var); ok {
			vc.Parameter[string(v)] = true
		}
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
		if !isExcluded(name) && !vc.Quantified[name] && !vc.Parameter[name] {
			vc.Local[name] = true
		}
	}
}

// collectVarsQuantified marks every variable in term as quantified, unless already local/parameter.
func collectVarsQuantified(term *ast.Term, vc *VarClassification) {
	collectVars(term, func(name string) {
		if !vc.Local[name] && !vc.Parameter[name] {
			vc.Quantified[name] = true
		}
	})
}
