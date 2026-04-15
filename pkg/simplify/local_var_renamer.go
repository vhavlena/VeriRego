package simplify

import (
	"fmt"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
	"github.com/vhavlena/verirego/pkg/util"
)

// LocalVarRenamer replaces local variables inside compiled Rego rules with
// globally unique fresh names, ensuring no two rules ever share a local
// variable name.
//
// A variable is considered local when [types.ClassifyVars] classifies it as
// such (i.e. it is the LHS of an assignment expression).
//
// The renaming lambda assigned inside [SimplifyRule] maintains an internal map
// so that every occurrence of the same variable within a rule is consistently
// replaced by the same fresh name.  Because [util.RenameLocalVarsInRule] calls
// the lambda per occurrence, no separate counting pass is needed.
//
// Usage:
//
//	r := simplify.NewLocalVarRenamer()
//	newModule := r.SimplifyModule(module)
type LocalVarRenamer struct {
	counter int
}

// NewLocalVarRenamer returns a ready-to-use LocalVarRenamer.
func NewLocalVarRenamer() *LocalVarRenamer {
	return &LocalVarRenamer{}
}

func (r *LocalVarRenamer) freshName() string {
	name := fmt.Sprintf("__lv%d", r.counter)
	r.counter++
	return name
}

// SimplifyModule returns a new module in which every local variable has been
// replaced by a fresh, globally unique name.  The original module is not mutated.
func (r *LocalVarRenamer) SimplifyModule(module *ast.Module) *ast.Module {
	newModule := *module
	newRules := make([]*ast.Rule, len(module.Rules))
	for i, rule := range module.Rules {
		newRules[i] = r.SimplifyRule(rule)
	}
	newModule.Rules = newRules
	return &newModule
}

// SimplifyRule returns a deep copy of rule in which every local variable (and
// every variable used as a head return value) has been replaced by a fresh,
// globally unique name.  The original rule is not mutated.
//
// Each else branch is treated as an independent scope: variables that share a
// name across the main branch and an else branch receive distinct fresh names.
// This is achieved by calling SimplifyRule recursively for each else branch
// with a fresh assigned map.
func (r *LocalVarRenamer) SimplifyRule(rule *ast.Rule) *ast.Rule {
	// Classify variables for this branch only (head value vars included as local).
	vc := types.ClassifyVarsBranch(rule)

	assigned := make(map[string]string)
	fn := func(_ string, _ int, varName string) (string, bool) {
		if newName, ok := assigned[varName]; ok {
			return newName, true
		}
		newName := r.freshName()
		assigned[varName] = newName
		return newName, true
	}
	// Each occurrence of "_" is independent, so give every one its own fresh name.
	wildcardFn := func(_ string, _ int, _ string) (string, bool) {
		return r.freshName(), true
	}

	// Build combined set: local + quantified variables are both renamed.
	allVars := make(map[string]bool, len(vc.Local)+len(vc.Quantified))
	for k := range vc.Local {
		allVars[k] = true
	}
	for k := range vc.Quantified {
		allVars[k] = true
	}
	// Function arguments define the call interface and must not be renamed:
	// they appear in Quantified (used in body expressions) but renaming them
	// only in the main branch while the else branch leaves them unchanged
	// would create inconsistent variable names across branches.
	for _, arg := range rule.Head.Args {
		if v, ok := arg.Value.(ast.Var); ok {
			delete(allVars, string(v))
		}
	}

	// Rename only this branch's head + body (not else).
	result := util.RenameVarsInBranchOnly(rule, 0, allVars, fn, wildcardFn)

	// Recurse into else branches independently, each with a fresh assigned map.
	if rule.Else != nil {
		result.Else = r.SimplifyRule(rule.Else)
	}
	return result
}
