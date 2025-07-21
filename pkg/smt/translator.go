package smt

import (
	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

// Translator is responsible for translating Rego terms to SMT expressions.
type Translator struct {
	TypeInfo     *types.TypeAnalyzer // Type information for Rego terms
	VarMap       map[string]string   // Mapping of Rego term keys to SMT variable names
	smtTypeDecls []string            // SMT type declarations
	smtDecls     []string            // SMT variable declarations
	smtAsserts   []string            // SMT assertions
	mod          *ast.Module
}

// NewTranslator creates a new Translator instance with the given TypeAnalyzer.
func NewTranslator(typeInfo *types.TypeAnalyzer, mod *ast.Module) *Translator {
	return &Translator{
		TypeInfo:     typeInfo,
		VarMap:       make(map[string]string),
		smtTypeDecls: make([]string, 0, 32),
		smtDecls:     make([]string, 0, 64),
		smtAsserts:   make([]string, 0, 128),
		mod:          mod,
	}
}

// SmtLines returns the generated SMT-LIB lines collected during translation, in the correct order.
//
// Returns:
//
//	[]string: A slice of SMT-LIB formatted strings representing the translation output.
func (t *Translator) SmtLines() []string {
	lines := make([]string, 0, len(t.smtTypeDecls)+len(t.smtDecls)+len(t.smtAsserts))
	lines = append(lines, t.smtTypeDecls...)
	lines = append(lines, t.smtDecls...)
	lines = append(lines, t.smtAsserts...)
	return lines
}

// InputParameterVars returns the string names of variables occurring as rule input parameters.
//
// Returns:
//
//	[]string: A slice of variable names (as strings) that appear as input parameters in rule heads.
func (t *Translator) InputParameterVars() []string {
	if t.mod == nil || t.mod.Rules == nil {
		return nil
	}
	var paramVars []string
	for _, rule := range t.mod.Rules {
		if rule == nil || rule.Head == nil || rule.Head.Args == nil {
			continue
		}
		for _, arg := range rule.Head.Args {
			if varTerm, ok := arg.Value.(ast.Var); ok {
				paramVars = append(paramVars, varTerm.String())
			}
		}
	}
	return paramVars
}

// getSmtVarsDeclare collects the global variables to be declared in SMT-LIB, excluding input parameters.
//
// Returns:
//
//	map[string]any: A map of variable names to empty structs, representing global variables to declare.
func (t *Translator) getSmtVarsDeclare() map[string]any {

	inputParams := t.InputParameterVars()
	inputParamSet := make(map[string]struct{}, len(inputParams))
	for _, v := range inputParams {
		inputParamSet[v] = struct{}{}
	}

	globalVars := make(map[string]any)
	if t.TypeInfo != nil {
		for name := range t.TypeInfo.Types {
			if _, isParam := inputParamSet[name]; !isParam {
				_, okVar := t.TypeInfo.Refs[name].(ast.Var)
				if okVar {
					globalVars[name] = struct{}{}
				}
			}
		}
	}
	globalVars["input.review.object"] = struct{}{} // Always include schema
	return globalVars
}

// GenerateSmtContent generates the SMT-LIB content for the current module.
//
// This function collects input parameter variables and global variables, then generates
// type definitions for the global variables using the TypeAnalyzer. The generated SMT-LIB
// lines are stored in the Translator's internal buffer.
//
// Returns:
//
//	error: An error if type definition generation fails, otherwise nil.
func (t *Translator) GenerateSmtContent() error {
	// Gather input parameter variables
	globalVars := t.getSmtVarsDeclare()
	if err := t.GenerateTypeDefs(globalVars); err != nil {
		return err
	}
	if err := t.TranslateModuleToSmt(); err != nil {
		return err
	}
	return nil
}

// TranslateModuleToSmt converts all rules in the Translator's module to SMT-LIB assertions.
//
// Each rule is translated using RuleToSmt and results in a single SMT-LIB (assert ...) statement.
//
// Returns:
//
//	error: An error if any rule conversion fails.
func (t *Translator) TranslateModuleToSmt() error {
	if t.mod == nil || t.mod.Rules == nil {
		return nil
	}
	for _, rule := range t.mod.Rules {
		if err := t.RuleToSmt(rule); err != nil {
			return err
		}
	}
	return nil
}
