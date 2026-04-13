package simplify

import (
	"fmt"

	"github.com/open-policy-agent/opa/v1/ast"
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

// SimplifyRule returns a deep copy of rule in which every local variable has
// been replaced by a fresh, globally unique name.  The original rule is not
// mutated.
//
// The lambda closes over an assigned map: the first occurrence of a variable
// triggers fresh-name allocation; subsequent occurrences reuse the same name.
func (r *LocalVarRenamer) SimplifyRule(rule *ast.Rule) *ast.Rule {
	assigned := make(map[string]string)
	fn := func(_ string, _ int, varName string) (string, bool) {
		if newName, ok := assigned[varName]; ok {
			return newName, true
		}
		newName := r.freshName()
		assigned[varName] = newName
		return newName, true
	}
	return util.RenameLocalVarsInRule(rule, 0, fn)
}
