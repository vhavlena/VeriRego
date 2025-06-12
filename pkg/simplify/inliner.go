// Package inlining provides support for inlining Rego functions in AST modules.
package simplify

import (
	"github.com/open-policy-agent/opa/ast"
)

type Inliner struct {
	inlinePreds map[string]*ast.Rule
}

// NewInliner creates a new Inliner with an empty inlinePreds map.
func NewInliner() *Inliner {
	return &Inliner{inlinePreds: make(map[string]*ast.Rule)}
}

// GatherInlinePredicates sets the inlinePreds map to rules that assign true and have only one expression in the body.
func (inl *Inliner) GatherInlinePredicates(module *ast.Module) {
	inl.inlinePreds = map[string]*ast.Rule{}
	for _, rule := range module.Rules {
		boolVal, ok := rule.Head.Value.Value.(ast.Boolean)
		if ok && boolVal == ast.Boolean(true) && len(rule.Body) == 1 {
			inl.inlinePreds[rule.Head.Name.String()] = rule
		}
	}
}

// inlineExpr replaces function calls in an expression with the inlined body.
func inlineExpr(expr *ast.Expr, funcDefs map[string]*ast.Rule) []*ast.Expr {
	call, ok := expr.Terms.([]*ast.Term)
	if !ok || len(call) == 0 {
		return []*ast.Expr{expr}
	}
	// Check if the first term is a function name
	funcName, ok := call[0].Value.(ast.Var)
	if !ok {
		return []*ast.Expr{expr}
	}
	def, ok := funcDefs[funcName.String()]
	if !ok {
		return []*ast.Expr{expr}
	}
	// Map arguments to parameters
	argMap := map[string]*ast.Term{}
	for i, param := range def.Head.Args {
		if i+1 < len(call) {
			if v, ok := param.Value.(ast.Var); ok {
				argMap[v.String()] = call[i+1]
			}
		}
	}
	// Substitute parameters in the function body
	inlinedBody := make([]*ast.Expr, 0, len(def.Body))
	for _, b := range def.Body {
		inlinedBody = append(inlinedBody, substituteVars(b, argMap))
	}
	return inlinedBody
}

// substituteVars replaces variables in an expression according to argMap.
func substituteVars(expr *ast.Expr, argMap map[string]*ast.Term) *ast.Expr {
	newExpr := *expr
	newExpr.Terms = substituteTerms(expr.Terms, argMap)
	return &newExpr
}

// substituteTerms recursively substitutes variables in terms or slices of terms.
func substituteTerms(terms interface{}, argMap map[string]*ast.Term) interface{} {
	switch t := terms.(type) {
	case *ast.Term:
		if v, ok := t.Value.(ast.Var); ok {
			if arg, found := argMap[v.String()]; found {
				return arg
			}
		}
		// Also substitute inside ast.Call
		if call, ok := t.Value.(ast.Call); ok {
			newCall := make(ast.Call, len(call))
			for i, term := range call {
				if newTerm, ok := substituteTerms(term, argMap).(*ast.Term); ok {
					newCall[i] = newTerm
				} else {
					newCall[i] = term
				}
			}
			return ast.NewTerm(newCall)
		}
		return t
	case []*ast.Term:
		newTerms := make([]*ast.Term, len(t))
		for i, term := range t {
			if newTerm, ok := substituteTerms(term, argMap).(*ast.Term); ok {
				newTerms[i] = newTerm
			} else {
				newTerms[i] = term
			}
		}
		return newTerms
	default:
		return terms
	}
}
