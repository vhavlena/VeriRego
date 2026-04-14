// Package util provides utility functions for Rego AST manipulation.
package util

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

// RenameFunc is called for each local-variable occurrence during the AST walk.
// It returns (newName, true) to rename the variable, or ("", false) to leave
// it unchanged.
//
// Because the function is called once per occurrence (not once per unique name),
// a stateful closure can assign a consistent fresh name on first encounter and
// return the same name for every subsequent occurrence of the same variable.
type RenameFunc func(ruleName string, ruleIdx int, varName string) (string, bool)

// DefaultRenameFunc always renames, appending the rule index so that
// identically named locals in different rules never collide.
//
// Example: rule index 2, variable "x"  →  "x__r2"
func DefaultRenameFunc(ruleName string, ruleIdx int, varName string) (string, bool) {
	return fmt.Sprintf("%s__r%d", varName, ruleIdx), true
}

// RenameLocalVarsInModule renames the local variables of every rule in module
// using fn.  Only variables classified as local by [types.ClassifyVars] are
// passed to fn; quantified variables and the special names ("_", "data",
// "input", "rego") are never renamed.
//
// The function operates on a deep copy of the module so the original is not
// mutated.
func RenameLocalVarsInModule(module *ast.Module, fn RenameFunc) *ast.Module {
	newModule := shallowCopyModule(module)
	newRules := make([]*ast.Rule, len(module.Rules))
	for i, rule := range module.Rules {
		newRules[i] = RenameLocalVarsInRule(rule, i, fn)
	}
	newModule.Rules = newRules
	return newModule
}

// RenameLocalVarsInRule renames the local variables of a single compiled Rego
// rule (including any else branches) using fn.  fn is invoked for every
// occurrence of a local variable in the AST; ruleIdx is forwarded unchanged so
// the caller can use it to generate globally unique names.
//
// The function operates on a deep copy of the rule so the original is not
// mutated.
func RenameLocalVarsInRule(rule *ast.Rule, ruleIdx int, fn RenameFunc) *ast.Rule {
	return RenameLocalAndWildcardVarsInRule(rule, ruleIdx, fn, nil)
}

// RenameLocalAndWildcardVarsInRule is like [RenameLocalVarsInRule] but also
// replaces every occurrence of an OPA-generated wildcard variable (names that
// start with "$", e.g. "$0", "$1") by calling wildcardFn.  OPA renames each
// "_" occurrence to a unique "$N" name during parsing, so wildcardFn is
// invoked once per variable occurrence and can return a distinct fresh name
// for each.  Pass nil for wildcardFn to leave wildcard variables unchanged
// (identical behaviour to [RenameLocalVarsInRule]).
func RenameLocalAndWildcardVarsInRule(rule *ast.Rule, ruleIdx int, fn RenameFunc, wildcardFn RenameFunc) *ast.Rule {
	vc := types.ClassifyVars(rule)
	w := &renameWalker{
		ruleName:   rule.Head.Name.String(),
		ruleIdx:    ruleIdx,
		localVars:  vc.Local,
		fn:         fn,
		wildcardFn: wildcardFn,
	}
	return w.inRule(rule)
}

// ──────────────────────────────────────────────────────────────────────────────
// renameWalker — deep-copies the AST while calling fn for each local-var occurrence
// ──────────────────────────────────────────────────────────────────────────────

type renameWalker struct {
	ruleName   string
	ruleIdx    int
	localVars  map[string]bool
	fn         RenameFunc
	wildcardFn RenameFunc
}

func (w *renameWalker) inRule(rule *ast.Rule) *ast.Rule {
	newRule := *rule
	newRule.Head = w.inHead(rule.Head)
	newBody := make(ast.Body, len(rule.Body))
	for i, expr := range rule.Body {
		newBody[i] = w.inExpr(expr)
	}
	newRule.Body = newBody
	if rule.Else != nil {
		newRule.Else = w.inRule(rule.Else)
	}
	return &newRule
}

func (w *renameWalker) inHead(head *ast.Head) *ast.Head {
	newHead := *head
	if head.Value != nil {
		newHead.Value = w.inTerm(head.Value)
	}
	if head.Key != nil {
		newHead.Key = w.inTerm(head.Key)
	}
	if len(head.Args) > 0 {
		newArgs := make(ast.Args, len(head.Args))
		for i, arg := range head.Args {
			newArgs[i] = w.inTerm(arg)
		}
		newHead.Args = newArgs
	}
	return &newHead
}

func (w *renameWalker) inExpr(expr *ast.Expr) *ast.Expr {
	newExpr := *expr
	newExpr.Terms = w.inTerms(expr.Terms)
	if len(expr.With) > 0 {
		newWith := make([]*ast.With, len(expr.With))
		for i, wt := range expr.With {
			nw := *wt
			nw.Target = w.inTerm(wt.Target)
			nw.Value = w.inTerm(wt.Value)
			newWith[i] = &nw
		}
		newExpr.With = newWith
	}
	return &newExpr
}

func (w *renameWalker) inTerms(terms interface{}) interface{} {
	switch t := terms.(type) {
	case *ast.Term:
		return w.inTerm(t)
	case []*ast.Term:
		newTerms := make([]*ast.Term, len(t))
		for i, term := range t {
			newTerms[i] = w.inTerm(term)
		}
		return newTerms
	default:
		return terms
	}
}

func (w *renameWalker) inTerm(term *ast.Term) *ast.Term {
	if term == nil {
		return nil
	}
	return ast.NewTerm(w.inValue(term.Value))
}

func (w *renameWalker) inValue(val ast.Value) ast.Value {
	switch v := val.(type) {
	case ast.Var:
		name := string(v)
		if strings.HasPrefix(name, "$") && w.wildcardFn != nil {
			if newName, ok := w.wildcardFn(w.ruleName, w.ruleIdx, name); ok {
				return ast.Var(newName)
			}
		}
		if w.localVars[name] {
			if newName, ok := w.fn(w.ruleName, w.ruleIdx, name); ok {
				return ast.Var(newName)
			}
		}
		return v

	case ast.Ref:
		newRef := make(ast.Ref, len(v))
		for i, seg := range v {
			newRef[i] = w.inTerm(seg)
		}
		return newRef

	case *ast.Array:
		elems := make([]*ast.Term, v.Len())
		for i := range v.Len() {
			elems[i] = w.inTerm(v.Elem(i))
		}
		return ast.NewArray(elems...)

	case ast.Object:
		newObj := ast.NewObject()
		v.Foreach(func(k, val *ast.Term) {
			newObj.Insert(w.inTerm(k), w.inTerm(val))
		})
		return newObj

	case ast.Set:
		newSet := ast.NewSet()
		v.Foreach(func(elem *ast.Term) {
			newSet.Add(w.inTerm(elem))
		})
		return newSet

	case ast.Call:
		newCall := make(ast.Call, len(v))
		for i, t := range v {
			newCall[i] = w.inTerm(t)
		}
		return newCall

	default:
		return val
	}
}

// shallowCopyModule returns a shallow copy of module with a fresh Rules slice.
func shallowCopyModule(module *ast.Module) *ast.Module {
	m := *module
	return &m
}
