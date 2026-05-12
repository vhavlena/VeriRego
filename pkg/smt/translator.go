package smt

import (
	"errors"
	"fmt"
	"maps"

	"github.com/open-policy-agent/opa/v1/ast"
	verr "github.com/vhavlena/verirego/pkg/err"

	"github.com/vhavlena/verirego/pkg/types"
)

type TransContext struct {
	VarMap map[string]string // Mapping of Rego term keys to SMT variable names
	Bucket *Bucket           // Bucket to collect generated SMT declarations and assertions
}

func NewTransContext() *TransContext {
	return &TransContext{
		VarMap: make(map[string]string),
		Bucket: NewBucket(),
	}
}

func NewTransContextWithVarMap(varMap map[string]string) *TransContext {
	return &TransContext{
		VarMap: varMap,
		Bucket: NewBucket(),
	}
}

//-------------------------------------------------------------

// Translator is responsible for translating Rego terms to SMT expressions.
type Translator struct {
	TypeTrans    *TypeTranslator     // Type definitions and type-related operations
	VarMap       map[string]string   // Mapping of Rego term keys to SMT variable names
	defaultsMap  map[string]SmtValue // Mapping of variable names to default values
	funcMap      map[string]Function // Mapping of function names to their representation
	freshNames   map[string]struct{} // Names already issued by FreshName, to prevent re-use
	smtTypeDecls []*SmtCommand       // SMT type declarations
	smtDecls     []*SmtCommand       // SMT variable declarations
	smtAsserts   []*SmtCommand       // SMT assertions
	mod          *ast.Module
}

// NewTranslator creates a new Translator instance with the given TypeAnalyzer.
func NewTranslator(typeInfo *types.TypeAnalyzer, mod *ast.Module) *Translator {
	t := &Translator{
		TypeTrans:    NewTypeDefs(typeInfo),
		VarMap:       make(map[string]string),
		defaultsMap:  make(map[string]SmtValue),
		funcMap:      GetBuiltinFuncMap(),
		freshNames:   make(map[string]struct{}),
		smtTypeDecls: make([]*SmtCommand, 0, 32),
		smtDecls:     make([]*SmtCommand, 0, 64),
		smtAsserts:   make([]*SmtCommand, 0, 128),
		mod:          mod,
	}
	t.generateFunctions()
	return t
}

// SmtLines returns the generated SMT-LIB lines collected during translation, in the correct order.
//
// Returns:
//
//	[]string: A slice of SMT-LIB formatted strings representing the translation output.
func (t *Translator) SmtLines() []string {
	lines := make([]string, 0, len(t.smtTypeDecls)+len(t.smtDecls)+len(t.smtAsserts))
	for _, c := range t.smtTypeDecls {
		lines = append(lines, c.String())
	}
	for _, c := range t.smtDecls {
		lines = append(lines, c.String())
	}
	for _, c := range t.smtAsserts {
		lines = append(lines, c.String())
	}
	return lines
}

// AppendBucket appends the contents of the provided Bucket into the
// Translator's internal SMT-LIB buffers.
//
// Parameters:
//
//	bucket *Bucket: Bucket whose TypeDecls, Decls and Asserts will be appended
//	to the Translator's internal slices (t.smtTypeDecls, t.smtDecls, t.smtAsserts).
func (t *Translator) AppendBucket(bucket *Bucket) {
	t.smtTypeDecls = append(t.smtTypeDecls, bucket.TypeDecls...)
	t.smtDecls = append(t.smtDecls, bucket.Decls...)
	t.smtAsserts = append(t.smtAsserts, bucket.Asserts...)
}

// generateFunctions populates the inner funcMap with function with resolved type definitions
func (t *Translator) generateFunctions() {
	for op, ft := range t.TypeTrans.TypeInfo.Types {
		if !ft.IsFunction() {
			continue
		}
		_, ok := t.funcMap[op]
		if ok {
			// TODO: generate warning: redefinition of function
			// e.g. defining `plus` would redefine builtin `+` operator
			// this is in accordance with Rego functionality
		}
		t.funcMap[op] = NewFunction(op, ft)
	}
}

// AddTransContext merges the provided translation context into the
// current Translator instance.
//
// Parameters:
//
//	context *TransContext: the translation context whose VarMap and
//	Bucket contents should be merged into the translator.
//
// Behavior:
//
//	Copies all entries from context.VarMap into t.VarMap (overwriting any
//	existing keys), and appends context.Bucket into the translator's
//	internal SMT buffers via AppendBucket.
func (t *Translator) AddTransContext(context *TransContext) {
	maps.Copy(t.VarMap, context.VarMap)
	t.AppendBucket(context.Bucket)
}

// FreshName returns a name of the form "base_N" (N ≥ 1) that does not collide
// with any known rule name (TypeInfo.Types) or any name previously issued by
// this method. The returned name is recorded so it is not issued again.
func (t *Translator) FreshName(base string) string {
	for i := 1; ; i++ {
		candidate := fmt.Sprintf("%s_%d", base, i)
		_, inTypes := t.TypeTrans.TypeInfo.Types[candidate]
		_, inFresh := t.freshNames[candidate]
		if !inTypes && !inFresh {
			t.freshNames[candidate] = struct{}{}
			return candidate
		}
	}
}

func (t *Translator) SetDefaultValue(varName string, value *SmtValue) error {
	if _, ok := t.defaultsMap[varName]; ok {
		return errors.New("redefinition of default value of " + varName)
	}
	t.defaultsMap[varName] = *value
	return nil
}

func (t *Translator) GetDefaultValue(varName string) (*SmtValue, error) {
	if def, ok := t.defaultsMap[varName]; ok {
		return &def, nil
	}
	if tp, ok := t.TypeTrans.TypeInfo.Types[varName]; ok {
		depth := max(tp.TypeDepth(), 0)
		def := NewSmtValue("OUndef", 0)
		return def.WrapToDepth(depth), nil
	}
	return nil, verr.ErrTypeNotFound(varName)
}

// IntoExprTranslator creates an ExprTranslator populated with values from given Translator
func (t *Translator) IntoExprTranslator() *ExprTranslator {
	return &ExprTranslator{
		TypeTrans:   t.TypeTrans,
		funcMap:     t.funcMap,
		context:     NewTransContextWithVarMap(t.VarMap),
		packagePath: &t.mod.Package.Path,
	}
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
	if t.TypeTrans.TypeInfo != nil {
		for name := range t.TypeTrans.TypeInfo.Types {
			if _, isParam := inputParamSet[name]; !isParam {
				tp := t.TypeTrans.TypeInfo.Types[name]
				// Skip function definitions: they describe call signatures, not
				// runtime variables that need SMT declarations.
				if tp.IsFunction() {
					continue
				}
				_, okVar := t.TypeTrans.TypeInfo.Refs[name].(ast.Var)
				if okVar {
					globalVars[name] = struct{}{}
				}
			}
		}
	}
	globalVars["input"] = struct{}{} // Always include input schema
	if t.TypeTrans.TypeInfo.DataSchema != nil {
		globalVars["data"] = struct{}{} // Include data schema when provided
	}
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

	bucket, err := t.TypeTrans.GenerateTypeDecls(globalVars)
	if err != nil {
		return err
	}
	t.AppendBucket(bucket)

	bucket, err = t.TypeTrans.GenerateVarDecls(globalVars)
	if err != nil {
		return err
	}
	t.AppendBucket(bucket)

	if err := t.TranslateModuleToSmt(); err != nil {
		return err
	}
	return nil
}

// TranslateModuleToSmt converts all rules in the Translator's module to SMT-LIB assertions.
//
// Default rules are processed first to populate the defaults map. Non-default rules are
// then grouped by name: a group with a single rule uses RuleToSmt (existing behaviour),
// while a group with multiple rules (incremental rules) is handled by IncrementalRulesToSmt,
// which emits one SMT function per occurrence and a top-level combinator using nested ite.
//
// Returns:
//
//	error: An error if any rule conversion fails.
func (t *Translator) TranslateModuleToSmt() error {
	if t.mod == nil || t.mod.Rules == nil {
		return nil
	}

	// First pass: register all default values before translating bodies.
	for _, rule := range t.mod.Rules {
		if rule.Default {
			if err := t.RuleToSmt(rule); err != nil {
				return err
			}
		}
	}

	// Group non-default rules by name, preserving order of first occurrence.
	type ruleGroup struct {
		name  string
		rules []*ast.Rule
	}
	seen := make(map[string]int)
	groups := make([]ruleGroup, 0)

	for _, rule := range t.mod.Rules {
		if rule.Default {
			continue
		}
		name := rule.Head.Name.String()
		if idx, ok := seen[name]; ok {
			groups[idx].rules = append(groups[idx].rules, rule)
		} else {
			seen[name] = len(groups)
			groups = append(groups, ruleGroup{name: name, rules: []*ast.Rule{rule}})
		}
	}

	for _, g := range groups {
		if len(g.rules) == 1 {
			if err := t.RuleToSmt(g.rules[0]); err != nil {
				return err
			}
		} else {
			if err := t.IncrementalRulesToSmt(g.name, g.rules); err != nil {
				return err
			}
		}
	}
	return nil
}
