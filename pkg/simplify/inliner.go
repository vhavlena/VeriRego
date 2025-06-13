// Package inlining provides support for inlining Rego functions in AST modules.
package simplify

import (
	"github.com/open-policy-agent/opa/ast"
)

type Inliner struct {
	inlinePreds map[string]*ast.Rule
}

// NewInliner creates a new Inliner with an empty inlinePreds map.
//
// Returns:
//
// *Inliner: A new Inliner instance.
func NewInliner() *Inliner {
	return &Inliner{inlinePreds: make(map[string]*ast.Rule)}
}

// GatherInlinePredicates sets the inlinePreds map to rules that assign true and have only one expression in the body.
//
// Parameters:
//
// module (*ast.Module): The AST module to scan for inlinable predicates.
func (inl *Inliner) GatherInlinePredicates(module *ast.Module) {
	inl.inlinePreds = map[string]*ast.Rule{}
	for _, rule := range module.Rules {
		boolVal, ok := rule.Head.Value.Value.(ast.Boolean)
		if ok && boolVal == ast.Boolean(true) && len(rule.Body) == 1 {
			inl.inlinePreds[rule.Head.Name.String()] = rule
		}
	}
}

// inlinePredicates replaces function calls in an expression with the inlined body.
//
// Parameters:
//
// expr (*ast.Expr): The expression to process.
// funcDefs (map[string]*ast.Rule): Map of function names to their rule definitions.
//
// Returns:
//
// []*ast.Expr: Slice of expressions with inlined function calls.
func inlinePredicates(expr *ast.Expr, funcDefs map[string]*ast.Rule) []*ast.Expr {
	call, ok := expr.Terms.([]*ast.Term)
	if !ok || len(call) == 0 {
		return []*ast.Expr{expr}
	}
	// Check if the first term is a function name
	funcName, ok := call[0].Value.(ast.Ref)
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
//
// Parameters:
//
// expr (*ast.Expr): The expression in which to substitute variables.
// argMap (map[string]*ast.Term): Map of variable names to argument terms.
//
// Returns:
//
// *ast.Expr: The expression with variables substituted.
func substituteVars(expr *ast.Expr, argMap map[string]*ast.Term) *ast.Expr {
	newExpr := *expr
	newExpr.Terms = substituteTerms(expr.Terms, argMap)
	return &newExpr
}

// substituteTerms recursively substitutes variables in terms or slices of terms.
//
// Parameters:
//
// terms (interface{}): The terms or slice of terms to process.
// argMap (map[string]*ast.Term): Map of variable names to argument terms.
//
// Returns:
//
// interface{}: The terms with variables substituted.
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

// InlineRuleBody replaces inlinable function calls in the rule's body with their inlined bodies.
//
// Parameters:
//
// rule (*ast.Rule): The rule whose body should be processed for inlining.
//
// Returns:
//
// []*ast.Expr: The new rule body with inlined expressions.
func (inl *Inliner) InlineRuleBody(rule *ast.Rule) []*ast.Expr {
	var newBody []*ast.Expr
	for _, expr := range rule.Body {
		inlined := inlinePredicates(expr, inl.inlinePreds)
		newBody = append(newBody, inlined...)
	}
	return newBody
}
