// Package types provides type analysis for Rego AST.
package types

import (
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
)

// TypeAnalyzer performs type analysis on Rego AST
type TypeAnalyzer struct {
	packagePath       ast.Ref
	Types             map[string]RegoTypeDef // Store types by string key
	Refs              map[string]ast.Value   // Map string keys back to original values
	Schema            InputSchemaAPI         // Schema for input.* references
	DataSchema        InputSchemaAPI         // Schema for data.* references
	VarClassification VarClassification      // Variable classification (local vs. quantified vs. parameter) across all rules
}

// NewTypeAnalyzer creates a new type analyzer.
//
// Parameters:
//
//	schema *InputSchema: The input schema to use for type inference.
//
// Returns:
//
//	*TypeAnalyzer: A new instance of TypeAnalyzer.
func NewTypeAnalyzer(schema InputSchemaAPI) *TypeAnalyzer {
	return &TypeAnalyzer{
		Types:  make(map[string]RegoTypeDef),
		Refs:   make(map[string]ast.Value),
		Schema: schema,
		VarClassification: VarClassification{
			Local:      make(map[string]bool),
			Quantified: make(map[string]bool),
			Parameter:  make(map[string]bool),
		},
	}
}

// NewTypeAnalyzerWithParams creates a new type analyzer.
//
// Parameters:
//
//	packagePath ast.Ref: The package path for the module being analyzed.
//	schema InputSchemaAPI: The input schema to use for type inference.
//
// Returns:
//
//	*TypeAnalyzer: A new instance of TypeAnalyzer.
func NewTypeAnalyzerWithParams(packagePath ast.Ref, schema InputSchemaAPI) *TypeAnalyzer {
	return &TypeAnalyzer{
		packagePath: packagePath,
		Types:       make(map[string]RegoTypeDef),
		Refs:        make(map[string]ast.Value),
		Schema:      schema,
		VarClassification: VarClassification{
			Local:      make(map[string]bool),
			Quantified: make(map[string]bool),
			Parameter:  make(map[string]bool),
		},
	}
}

// getValueKey returns a string key for an AST value.
//
// Parameters:
//
//	val ast.Value: The AST value to generate a key for.
//
// Returns:
//
//	string: The string key representing the value.
func (ta *TypeAnalyzer) getValueKey(val ast.Value) string {
	switch v := val.(type) {
	case ast.Ref:
		return v.String()
	case ast.Var:
		return string(v)
	default:
		return val.String()
	}
}

// GetType returns the type for a given AST value.
//
// Parameters:
//
//	val ast.Value: The AST value to get the type for.
//
// Returns:
//
//	RegoTypeDef: The inferred or cached type for the value.
func (ta *TypeAnalyzer) GetType(val ast.Value) RegoTypeDef {
	key := ta.getValueKey(val)
	if typ, exists := ta.Types[key]; exists {
		return typ
	}
	return ta.inferAstType(val, nil)
}

// setType sets the type for a value only if the new type is more precise than the existing one
//
// Parameters:
//
//	val ast.Value: The AST value to set the type for.
//	typ RegoTypeDef: The type to assign to the value.
//
// Promotion across kinds is intentionally not supported: IsMorePrecise returns
// false when the incoming and existing types have different, non-unknown kinds.
// This is by design — valid Rego never uses the same symbol as both a plain rule
// and a user-defined function, so cross-kind name collisions cannot occur in
// practice. If they did, the later setType call would be silently ignored.
func (ta *TypeAnalyzer) setType(val ast.Value, typ RegoTypeDef) {
	key := ta.getValueKey(val)
	if existingType, exists := ta.Types[key]; exists {
		// Only update if new type is more precise
		if !typ.IsMorePrecise(&existingType) {
			return
		}
	}
	ta.Types[key] = typ
	ta.Refs[key] = val
}

// addToType appends a type to the (possibly union) type associated with the
// given AST value in the analyzer. If the value already has a recorded type,
// that type is converted to a union (if necessary) and the provided `typ` is
// appended. The resulting union is canonicalized (duplicates removed,
// unknowns discarded when appropriate, and single-member unions simplified)
// before being stored back into the analyzer. The function also updates the
// `Refs` map to point back to the provided value.
//
// Parameters:
//
//	val ast.Value: the AST value whose type should be extended
//	typ RegoTypeDef: the type to add to the value's union
//
// Side effects: mutates `ta.Types` and `ta.Refs` in-place.
func (ta *TypeAnalyzer) addToType(val ast.Value, typ RegoTypeDef) {
	key := ta.getValueKey(val)

	tp := NewUnionType([]RegoTypeDef{})
	if existingType, exists := ta.Types[key]; exists {
		tp = *existingType.MakeUnion()
	}
	tp.Union = append(tp.Union, typ)
	tp.CanonizeUnion()
	ta.Types[key] = tp
	ta.Refs[key] = val
}

// InferTermType infers the type of an AST term by analyzing its value, optionally refining the type based on an expected type (inherType).
//
// Parameters:
//
//	term *ast.Term: The AST term to infer the type for.
//	inherType *RegoTypeDef: An optional expected type (e.g., from a function parameter) used to refine the inferred type for variables.
//
// Returns:
//
//	RegoTypeDef: The inferred (and possibly refined) type of the term.
func (ta *TypeAnalyzer) InferTermType(term *ast.Term, inherType *RegoTypeDef) RegoTypeDef {
	if term == nil {
		return NewUnknownType()
	}
	return ta.inferAstType(term.Value, inherType)
}

// InferExprType infers the type of an AST expression.
//
// Parameters:
//
//	expr *ast.Expr: The AST expression to infer the type for.
//
// Returns:
//
//	RegoTypeDef: The inferred type of the expression.
func (ta *TypeAnalyzer) InferExprType(expr *ast.Expr) RegoTypeDef {
	if expr == nil {
		return NewUnknownType()
	}

	// Handle `some k in collection` / `some k, v in collection` declarations.
	if sd, ok := expr.Terms.(*ast.SomeDecl); ok {
		ta.inferQuantifiedVarTypesInSomeDecl(sd)
		return NewAtomicType(AtomicBoolean)
	}

	term, ok := expr.Terms.(*ast.Term)
	if ok {
		// If the expression is a single term, infer its type directly
		return ta.InferTermType(term, nil)
	}

	// Handle different expression types based on Terms
	terms, ok := expr.Terms.([]*ast.Term)
	// fmt.Printf("Expression terms: %v %v\n", terms, ok)
	if !ok || len(terms) == 0 {
		return NewUnknownType()
	}

	// For simple expressions with a single term
	if len(terms) == 1 {
		return ta.InferTermType(terms[0], nil)
	}

	// Handle built-in operators and functions
	if expr.IsCall() {
		operator := terms[0]
		if isEquality(operator.String()) {
			tleft := ta.InferTermType(terms[1], nil)
			tright := ta.InferTermType(terms[2], nil)

			// Update types only for variables involved in equality
			if isVar(terms[1]) {
				ta.addToType(terms[1].Value, tright)
			}
			if isVar(terms[2]) {
				ta.addToType(terms[2].Value, tleft)
			}

			return NewAtomicType(AtomicBoolean)
		} else {
			// Handle function calls (user-defined functions are checked first)
			funcType, funcParams := ta.resolveFunctionType(operator.String(), len(terms)-1)
			for i := 1; i < len(terms); i++ {
				ta.InferTermType(terms[i], &funcParams[i-1])
			}
			ta.setType(terms[0].Value, funcType)
			return funcType
		}
	}

	// For comparison operators, return boolean type
	if expr.Operator() != nil {
		return NewAtomicType(AtomicBoolean)
	}

	// For all other cases, infer type from the first term
	return ta.InferTermType(terms[0], nil)
}

// inferAstType infers the type of an AST value, optionally refining the type based on an expected type (inherType).
//
// Parameters:
//
//	val ast.Value: The AST value to infer the type for.
//	inherType *RegoTypeDef: An optional expected type (e.g., from a function parameter) used to refine the inferred type for variables.
//
// Returns:
//
//	RegoTypeDef: The inferred (and possibly refined) type of the value.
func (ta *TypeAnalyzer) inferAstType(val ast.Value, inherType *RegoTypeDef) RegoTypeDef {
	if val == nil {
		return NewUnknownType()
	}

	// Use GetType to check for existing type (caching)
	key := ta.getValueKey(val)
	if typ, exists := ta.Types[key]; exists {
		// if type is unknown, try to make it more precise
		if !typ.IsUnknown() {
			return typ
		}
	}

	var typ RegoTypeDef
	switch v := val.(type) {
	case ast.String:
		typ = NewAtomicType(AtomicString)
	case ast.Number:
		typ = NewAtomicType(AtomicInt)
	case ast.Boolean:
		typ = NewAtomicType(AtomicBoolean)
	case *ast.Array:
		if v == nil || v.Len() == 0 {
			typ = NewArrayType(NewUnknownType())
		} else {
			var elementTypes []RegoTypeDef
			v.Foreach(func(elem *ast.Term) {
				elementTypes = append(elementTypes, ta.inferAstType(elem.Value, nil))
			})
			unionType := NewUnionType(elementTypes)
			unionType.CanonizeUnion()
			typ = NewArrayType(unionType)
		}
	case ast.Object:
		fields := make(map[string]RegoTypeDef)
		v.Foreach(func(key, val *ast.Term) {
			if str, ok := key.Value.(ast.String); ok {
				fields[string(str)] = ta.GetType(val.Value)
			}
		})
		typ = NewObjectType(fields)
	case ast.Set:
		typ = NewAtomicType(AtomicSet)
	case ast.Ref:
		typ = ta.inferRefType(v)
		ta.inferQuantifiedVarTypesInRef(v)
	case ast.Var:
		if t, exists := ta.Types[ta.getValueKey(v)]; exists {
			typ = t
		} else {
			typ = NewUnknownType()
		}
		if inherType != nil && inherType.IsMorePrecise(&typ) {
			typ = *inherType
		}
	case ast.Call:
		operator := v[0]
		funcType, funcParams := ta.resolveFunctionType(operator.String(), len(v)-1)
		for i := 1; i < len(v); i++ {
			ta.InferTermType(v[i], &funcParams[i-1])
		}
		return funcType
	default:
		typ = NewUnknownType()
	}

	ta.setType(val, typ)
	return typ
}

// inferRefType infers the type of a reference (e.g., input.x or data.x).
//
// Parameters:
//
//	ref ast.Ref: The reference to infer the type for.
//
// Returns:
//
//	RegoTypeDef: The inferred type of the reference.
func (ta *TypeAnalyzer) inferRefType(ref ast.Ref) RegoTypeDef {
	if len(ref) == 0 {
		return NewUnknownType()
	}

	head := ref[0].Value.String()
	// input prefix
	if head == "input" {
		if len(ref) > 1 && ta.Schema != nil {
			path := FromRef(ref[1:])
			if typ, exists := ta.Schema.GetType(path); exists && typ != nil {
				return *typ
			}
		}
	}

	// data prefix - check DataSchema for external data references
	if head == "data" && ta.DataSchema != nil {
		if len(ref) > 1 {
			path := FromRef(ref[1:])
			if typ, exists := ta.DataSchema.GetType(path); exists && typ != nil {
				return *typ
			}
		}
	}

	// data prefix - packagePath-based lookup for rules in the current package
	if ref.HasPrefix(ta.packagePath) && len(ref) > len(ta.packagePath) {
		strRule := ref[len(ta.packagePath)].Value.String()
		key := strRule[1 : len(strRule)-1]
		if typ, exists := ta.Types[key]; exists {
			path := FromRef(ref[len(ta.packagePath)+1:])
			if pathType, exists := typ.GetTypeFromPath(path); exists {
				return *pathType
			}
		}
	}

	// handle references to variables (arrays)
	refHead := ref[0].Value.String()
	if typ, exists := ta.Types[refHead]; exists {
		path := FromRef(ref[1:])
		if pathType, exists := typ.GetTypeFromPath(path); exists {
			return *pathType
		}
	}

	return NewUnknownType()
}

func (ta *TypeAnalyzer) GetPackagePath() *ast.Ref {
	return &ta.packagePath
}

// AnalyzeRule analyzes the given Rego rule and records the inferred type for the rule head.
//
// For parametric rules (functions) — those whose head carries at least one argument —
// analysis is delegated to analyzeParametricRule which produces a FunctionTypeDef.
// For plain rules AnalyzeRule constructs a union type to collect possible return types
// produced by the rule's body (including any else branches). It delegates the body analysis
// to AnalyzeRuleBody which appends discovered return types into the union. After analysis
// the union is canonicalized and stored in the analyzer's type map under the rule head's
// name via ta.setType.
//
// Side effects:
//   - mutates the provided TypeAnalyzer by recording the inferred type for the rule head
//     (via ta.setType and ta.Refs).
//
// Parameters:
//   - rule *ast.Rule: the Rego rule to analyze. The function expects a valid rule with a
//     head; behavior for malformed rules follows the underlying setType logic.
func (ta *TypeAnalyzer) AnalyzeRule(rule *ast.Rule) {
	if len(rule.Head.Args) > 0 {
		ta.analyzeParametricRule(rule)
		return
	}
	tp := NewUnionType([]RegoTypeDef{})
	ta.AnalyzeRuleBody(rule, &tp)
	tp.CanonizeUnion()
	ta.setType(rule.Head.Name, tp)
}

// analyzeParametricRule analyzes a Rego function / parametric rule and stores a
// FunctionTypeDef under the rule's name in the type map.
//
// The rule body is analyzed exactly as for plain rules; any type information inferred
// for the parameter variables (e.g. via equality constraints in the body or head value)
// is then collected and combined with the inferred return type to produce a
// KindFunction type definition.
//
// Parameters:
//   - rule *ast.Rule: a parametric rule (rule.Head.Args must be non-empty).
func (ta *TypeAnalyzer) analyzeParametricRule(rule *ast.Rule) {
	// Analyze the body and head value, collecting return types into tp.
	tp := NewUnionType([]RegoTypeDef{})
	ta.AnalyzeRuleBody(rule, &tp)
	tp.CanonizeUnion()

	// Collect inferred types for each parameter variable.
	paramTypes := make([]RegoTypeDef, len(rule.Head.Args))
	for i, arg := range rule.Head.Args {
		if v, ok := arg.Value.(ast.Var); ok {
			if t, exists := ta.Types[string(v)]; exists {
				paramTypes[i] = t
			} else {
				paramTypes[i] = NewUnknownType()
			}
		} else {
			paramTypes[i] = NewUnknownType()
		}
	}

	funcName := string(rule.Head.Name)
	funcType := NewFunctionType(funcName, paramTypes, tp)
	ta.setType(rule.Head.Name, funcType)
}

// lookupFunction searches the type map for a user-defined function by name.
//
// Two lookups are attempted in order:
//  1. Exact match on `name` (works for uncompiled modules where the operator is
//     the bare function name, e.g. "add_one").
//  2. Prefix-stripped match: if the analyzer has a package path and `name` starts
//     with "<packagePath>." (e.g. "data.test.add_one"), the prefix is removed and
//     the short name is looked up (handles fully-qualified references produced by
//     OPA's compiler).
//
// Returns the FunctionTypeDef if a KindFunction entry is found, or nil otherwise.
func (ta *TypeAnalyzer) lookupFunction(name string) *FunctionTypeDef {
	if ft, exists := ta.Types[name]; exists && ft.IsFunction() && ft.FunctionDef != nil {
		return ft.FunctionDef
	}
	if ta.packagePath != nil {
		prefix := ta.packagePath.String() + "."
		if strings.HasPrefix(name, prefix) {
			shortName := name[len(prefix):]
			if ft, exists := ta.Types[shortName]; exists && ft.IsFunction() && ft.FunctionDef != nil {
				return ft.FunctionDef
			}
		}
	}
	return nil
}

// resolveFunctionType returns the expected return type and parameter types for a
// function call. User-defined functions (stored as KindFunction entries in the type
// map) are checked first; the call falls back to the predefined-function registry.
//
// Two arities are accepted for user-defined functions:
//   - Exact match (len(ParamTypes) == arity): direct call, works for predicates and
//     uncompiled value-returning functions.
//   - Arity +1 (len(ParamTypes)+1 == arity): compiled value-returning function where
//     OPA appends the output variable as the last argument. In this case the last
//     parameter slot is given the function's return type so that the output variable
//     is correctly typed by the caller.
//
// Parameters:
//
//	name string: The function name as it appears in the call expression.
//	arity int: The number of arguments supplied at the call site.
//
// Returns:
//
//	RegoTypeDef: The expected return type.
//	[]RegoTypeDef: A fresh slice with the expected type for each argument position.
func (ta *TypeAnalyzer) resolveFunctionType(name string, arity int) (RegoTypeDef, []RegoTypeDef) {
	if fd := ta.lookupFunction(name); fd != nil {
		nParams := len(fd.ParamTypes)
		if nParams == arity {
			// Exact arity: predicate or uncompiled value-returning call.
			paramsCopy := make([]RegoTypeDef, nParams)
			copy(paramsCopy, fd.ParamTypes)
			return fd.ReturnType, paramsCopy
		}
		if nParams+1 == arity {
			// Compiled value-returning call: OPA appended the output variable as
			// the last argument. Propagate the return type to that slot so the
			// output variable inherits the correct type.
			paramsCopy := make([]RegoTypeDef, arity)
			copy(paramsCopy[:nParams], fd.ParamTypes)
			paramsCopy[nParams] = fd.ReturnType
			return fd.ReturnType, paramsCopy
		}
	}
	return funcParamsType(name, arity)
}

// AnalyzeRuleBody analyzes the body (and else branches) of a rule and appends discovered
// return types to the provided union type `tp`.
//
// tp must be a union type. This method infers types for each expression in the rule body
// (calling InferExprType) and, if the rule has a head value, infers the head's type and
// appends it to the union. If the rule contains an else branch, that branch is analyzed
// recursively and its return types are appended to the same union.
//
// The function mutates `tp` (by adding to tp.Union) and has no return value. It will
// panic if `tp` is not a union type.
//
// Parameters:
//   - rule *ast.Rule: the Rego rule whose body to analyze.
//   - tp *RegoTypeDef: pointer to a union RegoTypeDef that will be populated with the
//     possible return types discovered while analyzing the rule body and else branches.
func (ta *TypeAnalyzer) AnalyzeRuleBody(rule *ast.Rule, tp *RegoTypeDef) {
	if !tp.IsUnion() {
		panic("AnalyzeRuleBody: expected union type for rule with else branches")
	}
	// Analyze rule body
	for _, expr := range rule.Body {
		ta.InferExprType(expr)
	}
	// Analyze rule head value if it exists
	if rule.Head.Value != nil {
		returnType := ta.inferAstType(rule.Head.Value.Value, nil)
		tp.Union = append(tp.Union, returnType)
	}
	if rule.Else != nil {
		ta.AnalyzeRuleBody(rule.Else, tp)
	}
}

// AnalyzeModule performs iterative type analysis on all rules in a Rego module.
// After the type map converges, variable classifications (local vs. quantified)
// are computed once per rule and stored in RuleVarClassifications.
//
// Parameters:
//
//	mod *ast.Module: The Rego module to analyze.
func (ta *TypeAnalyzer) AnalyzeModule(mod *ast.Module) {
	var prevTypeMap map[string]RegoTypeDef
	// include input schema among types
	if ta.Schema != nil {
		ta.setType(ast.MustParseRef("input"), ta.Schema.GetTypes())
	}
	// include data schema among types
	if ta.DataSchema != nil {
		ta.setType(ast.MustParseRef("data"), ta.DataSchema.GetTypes())
	}
	// Classify variables upfront — the AST is static so this only needs to run once.
	for _, rule := range mod.Rules {
		ta.VarClassification.Merge(ClassifyVars(rule))
	}
	for {
		for _, rule := range mod.Rules {
			ta.AnalyzeRule(rule)
		}
		typeMap := ta.GetAllTypes()
		if prevTypeMap != nil && TypeMapEqual(prevTypeMap, typeMap) {
			break
		}
		prevTypeMap = CopyTypeMap(typeMap)
	}
}

// inferQuantifiedVarTypesInSomeDecl handles range-iteration declarations of
// the form `some k in collection` (OPA v1 syntax).  These are stored in the
// parsed AST as *ast.SomeDecl whose Symbols contain ast.Call nodes:
//
//   - internal.member_2(val, coll)       — value-only iteration
//   - internal.member_3(key, val, coll)  — key-value iteration
//
// For member_2, the value variable is inferred to have the value type of the
// collection.  For member_3, the key variable gets the index type (Int for
// arrays, String for objects) and the value variable gets the value type.
func (ta *TypeAnalyzer) inferQuantifiedVarTypesInSomeDecl(sd *ast.SomeDecl) {
	for _, sym := range sd.Symbols {
		call, ok := sym.Value.(ast.Call)
		if !ok || len(call) == 0 {
			continue
		}
		op := call[0].String()
		args := call[1:]
		switch op {
		case "internal.member_2":
			// member_2(val, coll)
			if len(args) == 2 {
				ta.inferMemberValueVarType(args[0], args[1])
			}
		case "internal.member_3":
			// member_3(key, val, coll)
			if len(args) == 3 {
				ta.inferMemberKeyVarType(args[0], args[2])
				ta.inferMemberValueVarType(args[1], args[2])
			}
		}
	}
}

// inferMemberValueVarType infers the type for a value variable in a membership
// expression. The value variable should take the element type of the collection
// (array element type, or union of object field values).
func (ta *TypeAnalyzer) inferMemberValueVarType(varTerm *ast.Term, collTerm *ast.Term) {
	v, ok := varTerm.Value.(ast.Var)
	if !ok {
		return
	}
	name := string(v)
	if isExcluded(name) {
		return
	}
	collType := ta.inferAstType(collTerm.Value, nil)
	// Value type = element type (array) or union of values (object).
	nonGroundPath := []PathNode{{Key: "_", IsGround: false}}
	if valType, found := collType.GetTypeFromPath(nonGroundPath); found && valType != nil {
		ta.addToType(v, *valType)
	}
}

// inferMemberKeyVarType infers the type for a key variable in a membership
// expression (Int for array index, String for object key).
func (ta *TypeAnalyzer) inferMemberKeyVarType(varTerm *ast.Term, collTerm *ast.Term) {
	v, ok := varTerm.Value.(ast.Var)
	if !ok {
		return
	}
	name := string(v)
	if isExcluded(name) {
		return
	}
	collType := ta.inferAstType(collTerm.Value, nil)
	if t := ta.indexTypeFromCollection(collType); t != nil {
		ta.addToType(v, *t)
	}
}

// inferQuantifiedVarTypesInRef inspects every non-head segment of ref. For
// each segment whose value is a variable (and whose name is not excluded), the
// function infers the index type from the collection type of the prefix ref
// that precedes this segment and records it via addToType — creating a union
// with any previously inferred type when appropriate:
//
//   - array collection → AtomicInt
//   - object collection → AtomicString
//
// The inferred type is recorded via addToType so the variable gets a proper
// entry in Types (and Refs) and downstream SMT translation can declare it.
func (ta *TypeAnalyzer) inferQuantifiedVarTypesInRef(ref ast.Ref) {
	for i := 1; i < len(ref); i++ {
		seg := ref[i]
		v, ok := seg.Value.(ast.Var)
		if !ok {
			continue
		}
		name := string(v)
		if isExcluded(name) {
			continue
		}

		// Determine the collection type from the prefix ref.
		prefixRef := ref[:i]
		collectionType := ta.inferRefType(prefixRef)

		indexType := ta.indexTypeFromCollection(collectionType)
		if indexType == nil {
			continue
		}
		ta.addToType(v, *indexType)
	}
}

// indexTypeFromCollection returns the expected type for a variable used as an
// index into collectionType:
//   - array  → *AtomicInt
//   - object → *AtomicString
//   - union  → union of all member index types
//
// Returns nil when the collection type does not determine an index type.
func (ta *TypeAnalyzer) indexTypeFromCollection(collectionType RegoTypeDef) *RegoTypeDef {
	switch {
	case collectionType.IsArray():
		t := NewAtomicType(AtomicInt)
		return &t
	case collectionType.IsObject():
		t := NewAtomicType(AtomicString)
		return &t
	case collectionType.IsUnion():
		typeList := []RegoTypeDef{}
		for _, member := range collectionType.Union {
			if t := ta.indexTypeFromCollection(member); t != nil {
				typeList = append(typeList, *t)
			}
		}
		tmp := NewUnionType(typeList)
		return &tmp
	}
	return nil
}

// GetVarClassification returns the flat VarClassification across all analysed rules.
func (ta *TypeAnalyzer) GetVarClassification() VarClassification {
	return ta.VarClassification
}

// GetAllTypes returns a copy of all inferred variable types.
//
// Returns:
//
//	map[string]RegoTypeDef: A map of variable names to their inferred types.
func (ta *TypeAnalyzer) GetAllTypes() map[string]RegoTypeDef {
	result := make(map[string]RegoTypeDef, len(ta.Types))
	for k, v := range ta.Types {
		result[k] = v
	}
	return result
}

// predefFunction applies predefined typing rules for a function if available.
// It mutates 'pars' in-place to set expected parameter types and returns the
// expected return type (or Unknown if not a predefined function or arity mismatch).
func predefFunction(name string, pars []RegoTypeDef) RegoTypeDef {
	if pf, ok := getPredefFunctions()[name]; ok {
		if pf.CheckArity == nil || pf.CheckArity(len(pars)) {
			if pf.UpdateParams != nil {
				pf.UpdateParams(pars)
			}
			return pf.ReturnType
		}
	}
	return NewUnknownType()
}

// funcParamsType returns the expected return type and parameter types for a given function name and parameter count.
//
// Parameters:
//
//	name string: The function name.
//	params int: The number of parameters for the function.
//
// Returns:
//
//	RegoTypeDef: The expected return type of the function.
//	[]RegoTypeDef: The expected types for each parameter.
func funcParamsType(name string, params int) (RegoTypeDef, []RegoTypeDef) {
	pars := make([]RegoTypeDef, params)
	for i := 0; i < params; i++ {
		pars[i] = NewUnknownType()
	}
	// First, try predefined function registry which can refine param and return types
	if ret := predefFunction(name, pars); !ret.IsUnknown() {
		return ret, pars
	}
	return NewUnknownType(), pars
}

// isEquality checks if a function name corresponds to an equality operation.
func isEquality(name string) bool {
	return IsEqualityOp(name)
}

// AnalyzeTypes is the main entry point for type analysis.
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule to analyze.
//	schema *InputSchema: The input schema for type inference.
//
// Returns:
//
//	*TypeAnalyzer: The type analyzer with inferred types.
func AnalyzeTypes(rule *ast.Rule, schema InputSchemaAPI) *TypeAnalyzer {
	analyzer := NewTypeAnalyzerWithParams(rule.Module.Package.Path, schema)
	analyzer.VarClassification.Merge(ClassifyVars(rule))
	analyzer.AnalyzeRule(rule)
	return analyzer
}
