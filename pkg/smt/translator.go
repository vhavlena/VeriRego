package smt

import (
	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

// Translator is responsible for translating Rego terms to SMT expressions.
type Translator struct {
	TypeInfo *types.TypeAnalyzer // Type information for Rego terms
	VarMap   map[string]string   // Mapping of Rego term keys to SMT variable names
	smtLines []string            // Collected SMT lines
	mod      *ast.Module
}

// NewTranslator creates a new Translator instance with the given TypeAnalyzer.
func NewTranslator(typeInfo *types.TypeAnalyzer, mod *ast.Module) *Translator {
	return &Translator{
		TypeInfo: typeInfo,
		VarMap:   make(map[string]string),
		smtLines: make([]string, 0, 128),
		mod:      mod,
	}
}

// SmtLines returns the generated SMT-LIB lines collected during translation.
//
// Returns:
//
//	[]string: A slice of SMT-LIB formatted strings representing the translation output.
func (t *Translator) SmtLines() []string {
	return t.smtLines
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
	inputParams := t.InputParameterVars()
	inputParamSet := make(map[string]struct{}, len(inputParams))
	for _, v := range inputParams {
		inputParamSet[v] = struct{}{}
	}

	// Gather global variables: those in TypeInfo.Types not in inputParams
	globalVars := make(map[string]any)
	if t.TypeInfo != nil {
		for name := range t.TypeInfo.Types {
			if _, isParam := inputParamSet[name]; !isParam {
				globalVars[name] = struct{}{}
			}
		}
	}
	if err := t.GenerateTypeDefs(globalVars); err != nil {
		return err
	}

	return nil
}
