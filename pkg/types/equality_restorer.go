package types

import (
	"fmt"

	"github.com/open-policy-agent/opa/v1/ast"
)

// RestoreEqualityOperators restores the "equal" operator in the compiled module
// for expressions that were originally written as == in the source. OPA
// compilation collapses =, ==, and := all into the "eq" operator; this pass
// re-distinguishes pure equality checks so downstream phases (type inference,
// SMT translation) do not need a separate location map.
//
// Call this after all other simplification passes (renaming, inlining), passing
// the original parsed module and the fully simplified compiled module.
func RestoreEqualityOperators(parsed, compiled *ast.Module) *ast.Module {
	locs := collectEqualityLocs(parsed)
	if len(locs) == 0 {
		return compiled
	}
	for _, rule := range compiled.Rules {
		ast.WalkExprs(rule, func(e *ast.Expr) bool {
			terms, ok := e.Terms.([]*ast.Term)
			if !ok || len(terms) == 0 || e.Location == nil {
				return false
			}
			if terms[0].String() == "eq" && locs[exprLocKey(e)] {
				terms[0] = ast.NewTerm(ast.Var("equal"))
			}
			return false
		})
	}
	return compiled
}

// collectEqualityLocs returns the source locations of all == expressions in the
// parsed module. In the parsed AST, == is represented with the operator string
// "equal" (distinct from = which is "eq").
func collectEqualityLocs(mod *ast.Module) map[string]bool {
	locs := make(map[string]bool)
	for _, rule := range mod.Rules {
		ast.WalkExprs(rule, func(e *ast.Expr) bool {
			terms, ok := e.Terms.([]*ast.Term)
			if ok && len(terms) > 0 && terms[0].String() == "equal" && e.Location != nil {
				locs[exprLocKey(e)] = true
			}
			return false
		})
	}
	return locs
}

func exprLocKey(expr *ast.Expr) string {
	if expr.Location == nil {
		return ""
	}
	return fmt.Sprintf("%s:%d:%d", expr.Location.File, expr.Location.Row, expr.Location.Col)
}
