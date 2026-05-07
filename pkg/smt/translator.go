package smt

import (
	"errors"
	"fmt"
	"maps"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	verr "github.com/vhavlena/verirego/pkg/err"

	"github.com/vhavlena/verirego/pkg/types"
)

// TranslatorOptions holds optional configuration for a Translator.
type TranslatorOptions struct {
	Prefix           string // SMT symbol prefix applied to all rule-head names
	EntryPoint       string // Rule name whose bodies are aggregated by GenerateEntryPointPredicate
	EntryPointOutput string // SMT symbol name for the aggregate define-fun (defaults to EntryPoint)
}

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
	TypeTrans        *TypeTranslator     // Type definitions and type-related operations
	VarMap           map[string]string   // Mapping of Rego term keys to SMT variable names
	defaultsMap      map[string]SmtValue // Mapping of variable names to default values
	funcMap          map[string]Function // Mapping of function names to their representation
	smtTypeDecls     []*SmtCommand       // SMT type declarations
	smtDecls         []*SmtCommand       // SMT variable declarations
	smtAsserts       []*SmtCommand       // SMT assertions
	mod               *ast.Module
	prefix            string      // SMT symbol prefix for all rule-head names
	entryPoint        string      // rule name to aggregate in GenerateEntryPointPredicate
	entryPointOutput  string      // SMT name for the aggregate define-fun (defaults to entryPoint)
	entryPointBodies  []*SmtValue // rule bodies collected for the entry point
}

// NewTranslator creates a new Translator instance with the given TypeAnalyzer.
func NewTranslator(typeInfo *types.TypeAnalyzer, mod *ast.Module) *Translator {
	t := &Translator{
		TypeTrans:        NewTypeDefs(typeInfo),
		VarMap:           make(map[string]string),
		defaultsMap:      make(map[string]SmtValue),
		funcMap:          GetBuiltinFuncMap(),
		smtTypeDecls:     make([]*SmtCommand, 0, 32),
		smtDecls:         make([]*SmtCommand, 0, 64),
		smtAsserts:       make([]*SmtCommand, 0, 128),
		mod:              mod,
		entryPointBodies: make([]*SmtValue, 0),
	}
	t.generateFunctions()
	return t
}

// NewTranslatorWithOptions creates a Translator with optional prefix and entry-point settings.
func NewTranslatorWithOptions(typeInfo *types.TypeAnalyzer, mod *ast.Module, opts TranslatorOptions) *Translator {
	t := NewTranslator(typeInfo, mod)
	t.prefix = opts.Prefix
	t.entryPoint = opts.EntryPoint
	t.entryPointOutput = opts.EntryPointOutput
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

// ruleHeadNames returns the set of rule-head names present in the module.
func (t *Translator) ruleHeadNames() map[string]bool {
	names := make(map[string]bool)
	if t.mod == nil {
		return names
	}
	for _, rule := range t.mod.Rules {
		if rule != nil && rule.Head != nil {
			names[rule.Head.Name.String()] = true
		}
	}
	return names
}

// smtVarName returns the SMT symbol name for a global variable.
// Rule-head names are prefixed with t.prefix; all other names are returned unchanged.
func (t *Translator) smtVarName(name string, ruleHeads map[string]bool) string {
	if t.prefix != "" && ruleHeads[name] {
		return t.prefix + name
	}
	return name
}

// generatePrefixedVarDecls generates variable declarations for usedVars, applying
// t.prefix to rule-head symbols so that declare-fun and assertions share the same name.
func (t *Translator) generatePrefixedVarDecls(usedVars map[string]any, ruleHeads map[string]bool) (*Bucket, error) {
	bucket := NewBucket()
	for name := range usedVars {
		smtName := t.smtVarName(name, ruleHeads)
		varBucket, err := t.TypeTrans.GenerateVarDeclAs(name, smtName)
		if err != nil {
			return nil, err
		}
		bucket.Append(varBucket)
	}
	return bucket, nil
}

// GetDeclaredSmtVars returns a map from original variable name to the SMT symbol
// used in the generated declarations (rule-head names carry t.prefix).
func (t *Translator) GetDeclaredSmtVars() map[string]string {
	globalVars := t.getSmtVarsDeclare()
	ruleHeads := t.ruleHeadNames()
	result := make(map[string]string, len(globalVars))
	for name := range globalVars {
		result[name] = t.smtVarName(name, ruleHeads)
	}
	return result
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
	globalVars := t.getSmtVarsDeclare()

	bucket, err := t.TypeTrans.GenerateTypeDecls(globalVars)
	if err != nil {
		return err
	}
	t.AppendBucket(bucket)

	// When a prefix is set, rule-head declare-funs must also carry the prefix so
	// that every occurrence of the symbol is consistent across the SMT program.
	if t.prefix != "" {
		ruleHeads := t.ruleHeadNames()
		bucket, err = t.generatePrefixedVarDecls(globalVars, ruleHeads)
	} else {
		bucket, err = t.TypeTrans.GenerateVarDecls(globalVars)
	}
	if err != nil {
		return err
	}
	t.AppendBucket(bucket)

	if err := t.TranslateModuleToSmt(); err != nil {
		return err
	}
	if t.entryPoint != "" {
		if err := t.GenerateEntryPointPredicate(); err != nil {
			return err
		}
	}
	return nil
}

// GenerateEntryPointPredicate emits a single aggregating define-fun that combines
// the bodies of all non-default rules whose head matches t.entryPoint.
// The output symbol is t.prefix+t.entryPointOutput when set, otherwise t.prefix+t.entryPoint.
//
// For atomic-boolean entry points:
//
//	(define-fun <out> () OTypeD0
//	  (ite (or (= body1 (OBoolean true)) ...) (OBoolean true) <default>))
//
// For all other types the aggregate returns the first non-undef body via a
// right-fold ITE chain:
//
//	(ite (not (is-OUndef body1)) body1
//	  (ite (not (is-OUndef body2)) body2
//	    OUndef))
func (t *Translator) GenerateEntryPointPredicate() error {
	if t.entryPoint == "" || len(t.entryPointBodies) == 0 {
		return nil
	}

	outputName := t.entryPointOutput
	if outputName == "" {
		outputName = t.entryPoint
	}

	var depth int
	isBoolAtomic := false
	if tp, ok := t.TypeTrans.TypeInfo.Types[t.entryPoint]; ok {
		depth = max(tp.TypeDepth(), 0)
		isBoolAtomic = tp.IsAtomic() && tp.AtomicType == types.AtomicBoolean
	}

	smtType := NewSmtType(uint(depth))

	var bodyExpr string
	if isBoolAtomic {
		// Build a Bool-typed (or ...) of equality checks, then wrap in ite.
		trueVal := "(OBoolean true)"
		defaultVal, err := t.GetDefaultValue(t.entryPoint)
		if err != nil || defaultVal == nil {
			defaultVal = NewSmtValue("OUndef", 0)
		}
		parts := make([]string, len(t.entryPointBodies))
		for i, b := range t.entryPointBodies {
			parts[i] = fmt.Sprintf("(= %s %s)", b.WrapToDepth(depth).String(), trueVal)
		}
		var cond string
		if len(parts) == 1 {
			cond = parts[0]
		} else {
			cond = fmt.Sprintf("(or %s)", strings.Join(parts, " "))
		}
		bodyExpr = fmt.Sprintf("(ite %s %s %s)", cond, trueVal, defaultVal.WrapToDepth(depth).String())
	} else {
		// Right-fold ITE chain: return the first body that is not OUndef.
		// is-OUndef is applied after unwrapping to depth 0 (consistent with IsUndef).
		fallback := NewSmtValue("OUndef", 0).WrapToDepth(depth).String()
		expr := fallback
		for i := len(t.entryPointBodies) - 1; i >= 0; i-- {
			b := t.entryPointBodies[i].WrapToDepth(depth)
			isUndef := fmt.Sprintf("(is-OUndef %s)", b.UnwrapToDepth(0).String())
			expr = fmt.Sprintf("(ite (not %s) %s %s)", isUndef, b.String(), expr)
		}
		bodyExpr = expr
	}

	cmd := RawCommand(fmt.Sprintf("(define-fun %s%s () %s %s)", t.prefix, outputName, smtType, bodyExpr))
	t.smtAsserts = append(t.smtAsserts, cmd)
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
