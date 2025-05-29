// Package types provides type analysis for Rego AST.
package types

import (
	"strings"

	"github.com/open-policy-agent/opa/ast"
)

// RegoType represents the possible types in Rego.
type RegoType string

const (
	TypeString   RegoType = "string"
	TypeInt      RegoType = "int"
	TypeObject   RegoType = "object"
	TypeArray    RegoType = "array"
	TypeBoolean  RegoType = "boolean"
	TypeSet      RegoType = "set"
	TypeUnknown  RegoType = "unknown"
	TypeFunction RegoType = "function"
	TypeIndex    RegoType = "index" // For variables used as array indices

	// Minimum reference length for array indexing.
	minRefLength = 2
)

// TypeInfo stores type information for variables and expressions.
type TypeInfo struct {
	types       map[string]RegoType
	ruleTypes   map[string]RegoType // Store types for rules
	InputSchema *InputSchema
	// Track which input path each variable represents
	varPaths map[string]string
}

// TypeVisitor implements type analysis for Rego AST.
type TypeVisitor struct {
	typeInfo *TypeInfo
}

// NewTypeVisitor creates a new TypeVisitor instance
func NewTypeVisitor() *TypeVisitor {
	return &TypeVisitor{
		typeInfo: NewTypeInfo(),
	}
}

// NewTypeInfo creates a new TypeInfo instance
func NewTypeInfo() *TypeInfo {
	return &TypeInfo{
		types:       make(map[string]RegoType),
		ruleTypes:   make(map[string]RegoType),
		InputSchema: NewInputSchema(),
		varPaths:    make(map[string]string),
	}
}

// buildInputPath constructs a dot-separated path starting with "input"
func (v *TypeVisitor) buildInputPath(ref ast.Ref) (string, []ast.Var) {
	var pathParts []string
	var variables []ast.Var

	pathParts = append(pathParts, "input")
	for _, term := range ref {
		if str, ok := term.Value.(ast.String); ok {
			pathParts = append(pathParts, string(str))
		} else if variable, ok := term.Value.(ast.Var); ok {
			variables = append(variables, variable)
		}
	}

	return strings.Join(pathParts, "."), variables
}

// handleArrayVariables marks variables as indices for array access
func (v *TypeVisitor) handleArrayVariables(variables []ast.Var) {
	for _, variable := range variables {
		v.promoteType(string(variable), TypeIndex)
	}
}

func (v *TypeVisitor) inferInputRefType(ref ast.Ref) RegoType {
	if len(ref) == 0 {
		return TypeObject
	}

	path, variables := v.buildInputPath(ref)

	// Check if we have schema information for this path
	if schemaType, exists := v.typeInfo.InputSchema.types[path]; exists {
		if schemaType == TypeArray {
			v.handleArrayVariables(variables)
		}
		return schemaType
	}

	// Default behavior for unknown paths
	v.handleArrayVariables(variables)
	return TypeObject
}

/**
 * VisitExpr analyzes types in an expression. It processes assignments, function calls, and comprehensions in the AST.
 * @param {*ast.Expr} expr - The expression to analyze
 */
func (v *TypeVisitor) VisitExpr(expr *ast.Expr) {
	if expr == nil {
		return
	}

	v.handleAssignments(expr)
	v.handleFunctionCalls(expr)
	v.handleComprehensions(expr)
}

/**
 * handleAssignments processes assignments and references in Rego expressions.
 * It handles both direct assignments and term references.
 * @param {*ast.Expr} expr - The expression to analyze
 */
func (v *TypeVisitor) handleAssignments(expr *ast.Expr) {
	if expr.IsAssignment() || expr.IsEquality() {
		v.handleDirectAssignment(expr)
		return
	}

	v.handleTermReferences(expr)
}

/**
 * handleDirectAssignment processes direct := assignments in Rego.
 * It infers the type of the right-hand side and assigns it to the left-hand side variable.
 * @param {*ast.Expr} expr - The assignment expression to analyze
 */
func (v *TypeVisitor) handleDirectAssignment(expr *ast.Expr) {
	// Get the RHS value
	rhs := expr.Operand(1).Value

	// Handle LHS variable
	if variable, ok := expr.Operand(0).Value.(ast.Var); ok {
		varName := string(variable)

		// If RHS is a reference, store the path
		if ref, ok := rhs.(ast.Ref); ok {
			path := v.buildRefPath(ref)
			v.typeInfo.varPaths[varName] = path
		}

		// Get the type
		valueType := v.inferType(rhs)
		v.promoteType(varName, valueType)
	}
}

// buildRefPath constructs a dot-separated path from a reference
func (v *TypeVisitor) buildRefPath(ref ast.Ref) string {
	var pathParts []string

	for _, term := range ref {
		if str, ok := term.Value.(ast.String); ok {
			pathParts = append(pathParts, string(str))
		} else if variable, ok := term.Value.(ast.Var); ok {
			pathParts = append(pathParts, string(variable))
		}
	}

	return strings.Join(pathParts, ".")
}

/**
 * handleTermReferences processes variable references in terms.
 * It analyzes both simple variable references and array indexing operations.
 * @param {*ast.Expr} expr - The expression containing the terms to analyze
 */
func (v *TypeVisitor) handleTermReferences(expr *ast.Expr) {
	if terms, ok := expr.Terms.([]*ast.Term); ok {
		v.processVariableTerms(terms)
		v.processArrayIndexing(terms)
	}
}

/**
 * processVariableTerms handles individual variable terms.
 * It extracts variables from terms and updates their type information.
 * @param {[]*ast.Term} terms - The terms to process
 */
func (v *TypeVisitor) processVariableTerms(terms []*ast.Term) {
	for _, term := range terms {
		if variable, ok := term.Value.(ast.Var); ok {
			varName := string(variable)
			v.promoteType(varName, v.inferType(variable))
		}
	}
}

/**
 * processArrayIndexing handles array indexing references.
 * Processes array index access expressions in the AST.
 * @param {[]*ast.Term} terms - The terms to check for array indexing
 */
func (v *TypeVisitor) processArrayIndexing(terms []*ast.Term) {
	if len(terms) > 0 {
		if ref, ok := terms[0].Value.(ast.Ref); ok {
			if len(ref) >= minRefLength {
				v.handleReference(ref)
			}
		}
	}
}

// handleReference processes Rego references like input.roles[i].
func (v *TypeVisitor) handleReference(ref ast.Ref) {
	// Handle array indexing variables
	for i := 1; i < len(ref); i++ {
		if term := ref[i]; term != nil {
			if variable, ok := term.Value.(ast.Var); ok {
				// If the previous segment is an array type, this variable is an index
				prevType := v.inferRefType(ref[:i])
				if prevType == TypeArray {
					v.promoteType(string(variable), TypeIndex)
				}
			}
		}
	}

	// Infer type from reference path
	if refType := v.inferRefType(ref); refType != TypeUnknown {
		if lastTerm := ref[len(ref)-1]; lastTerm != nil {
			if variable, ok := lastTerm.Value.(ast.Var); ok {
				v.promoteType(string(variable), refType)
			}
		}
	}
}

/**
 * handleFunctionCalls processes built-in function calls in the Rego AST.
 * It analyzes function references and infers types for their arguments.
 * @param {*ast.Expr} expr - The expression to analyze
 */
func (v *TypeVisitor) handleFunctionCalls(expr *ast.Expr) {
	if terms, ok := expr.Terms.([]*ast.Term); ok && len(terms) > 0 {
		if ref, ok := terms[0].Value.(ast.Ref); ok {
			v.inferFunctionTypes(ref.String(), terms[1:])
		}
	}
}

/**
 * handleComprehensions processes array and set comprehensions in the Rego AST.
 * It visits the comprehension body and sets appropriate types for the results.
 * @param {*ast.Expr} expr - The expression containing comprehensions to analyze
 */
func (v *TypeVisitor) handleComprehensions(expr *ast.Expr) {
	if terms, ok := expr.Terms.([]*ast.Term); ok {
		v.processComprehensionTerms(terms, expr)
	}
}

// processComprehensionTerms handles the actual comprehension processing to reduce complexity.
func (v *TypeVisitor) processComprehensionTerms(terms []*ast.Term, expr *ast.Expr) {
	for _, term := range terms {
		if arrayComp, ok := term.Value.(*ast.ArrayComprehension); ok {
			v.processArrayComprehension(arrayComp, expr)
		} else if setComp, ok := term.Value.(*ast.SetComprehension); ok {
			v.processSetComprehension(setComp, expr)
		}
	}
}

// processArrayComprehension handles array comprehension analysis.
func (v *TypeVisitor) processArrayComprehension(arrayComp *ast.ArrayComprehension, expr *ast.Expr) {
	for _, e := range arrayComp.Body {
		v.VisitExpr(e)
	}
	if variable, ok := expr.Operand(0).Value.(ast.Var); ok {
		v.promoteType(string(variable), TypeArray)
	}
}

// processSetComprehension handles set comprehension analysis.
func (v *TypeVisitor) processSetComprehension(setComp *ast.SetComprehension, expr *ast.Expr) {
	for _, e := range setComp.Body {
		v.VisitExpr(e)
	}
	if variable, ok := expr.Operand(0).Value.(ast.Var); ok {
		v.promoteType(string(variable), TypeSet)
	}
}

/**
 * inferFunctionTypes infers types for built-in function arguments based on the function name.
 * It categorizes functions into string operations, numeric operations, and boolean operations,
 * and assigns appropriate types to their arguments.
 * @param {string} funcName - The name of the function being called
 * @param {[]*ast.Term} args - The arguments passed to the function
 */
func (v *TypeVisitor) inferFunctionTypes(funcName string, args []*ast.Term) {
	stringOps := map[string]bool{
		"contains":   true,
		"startswith": true,
		"endswith":   true,
		"trim":       true,
		"replace":    true,
		"concat":     true,
		"format":     true,
		"lower":      true,
		"upper":      true,
		"split":      true,
	}

	numericOps := map[string]bool{
		"plus":  true,
		"minus": true,
		"mul":   true,
		"div":   true,
		"gt":    true,
		"lt":    true,
		"gte":   true,
		"lte":   true,
	}

	booleanOps := map[string]bool{
		"equal": true,
		"neq":   true,
		"and":   true,
		"or":    true,
		"not":   true,
	}

	switch {
	case stringOps[funcName]:
		v.assignArgsType(args, TypeString)
	case numericOps[funcName]:
		v.assignArgsType(args, TypeInt)
	case booleanOps[funcName]:
		v.assignArgsType(args, TypeBoolean)
	default:
		v.processVariableTerms(args)
	}
}

// assignArgsType assigns types to function arguments.
func (v *TypeVisitor) assignArgsType(args []*ast.Term, typ RegoType) {
	for _, arg := range args {
		if variable, ok := arg.Value.(ast.Var); ok {
			v.promoteType(variable.String(), typ)
		}
	}
}

/**
 * inferRefType infers the type of a reference path in Rego.
 * Handles both input.* and data.* references according to common patterns.
 * @param {ast.Ref} ref - The reference path to analyze
 * @return {RegoType} The inferred type of the reference
 */
func (v *TypeVisitor) inferRefType(ref ast.Ref) RegoType {
	if len(ref) == 0 {
		return TypeUnknown
	}

	// Check for variable-based path
	if typ := v.inferVarRefType(ref); typ != TypeUnknown {
		return typ
	}

	// Existing reference handling
	head := ref[0].Value.String()
	switch head {
	case "data":
		return v.inferDataRefType(ref[1:])
	default:
		return v.inferInputRefType(ref[1:])
	}
}

// inferVarRefType handles type inference for variable-based references
func (v *TypeVisitor) inferVarRefType(ref ast.Ref) RegoType {
	if len(ref) == 0 {
		return TypeUnknown
	}

	variable, ok := ref[0].Value.(ast.Var)
	if !ok {
		return TypeUnknown
	}

	storedPath, exists := v.typeInfo.varPaths[string(variable)]
	if !exists {
		return TypeUnknown
	}

	// Combine stored path with remaining reference parts
	remainingPath := v.buildRefPath(ref[1:])
	if remainingPath != "" {
		fullPath := storedPath + "." + remainingPath
		if typ, exists := v.typeInfo.InputSchema.types[fullPath]; exists {
			return typ
		}
	}

	// Return the type of the stored path if we have it
	if typ, exists := v.typeInfo.InputSchema.types[storedPath]; exists {
		return typ
	}

	return TypeUnknown
}

/**
 * inferDataRefType infers types for data.* references.
 * Currently returns unknown type, should be implemented based on data structure.
 * @param {ast.Ref} ref - The reference to analyze
 * @return {RegoType} The inferred type for the data reference
 */
func (v *TypeVisitor) inferDataRefType(ref ast.Ref) RegoType {
	return TypeUnknown // Implement based on your data structure
}

/**
 * isMorePrecise determines if newType is more precise than existingType.
 * Precision hierarchy: {Int, String} > Index > Array > Object > Unknown
 * @param {RegoType} newType - The new type to compare
 * @param {RegoType} existingType - The existing type to compare against
 * @return {bool} True if newType is more precise than existingType
 */
func (v *TypeVisitor) isMorePrecise(newType, existingType RegoType) bool {
	if existingType == TypeUnknown {
		return true
	}

	if existingType == TypeIndex {
		return newType == TypeInt || newType == TypeString
	}

	if existingType == TypeObject {
		return newType == TypeArray
	}

	return false
}

/**
 * promoteType sets the type information for a given variable name.
 * Only updates the type if the new type is more precise than the existing one.
 * @param {string} varName - The name of the variable to set the type for
 * @param {RegoType} typ - The type to set for the variable
 */
func (v *TypeVisitor) promoteType(varName string, typ RegoType) {
	existingType, exists := v.typeInfo.types[varName]
	if !exists || v.isMorePrecise(typ, existingType) {
		v.typeInfo.types[varName] = typ
	}
}

/**
 * promoteRuleType sets the type information for a given rule name.
 * Only updates the type if the new type is more precise than the existing one.
 * @param {string} ruleName - The name of the rule to set the type for
 * @param {RegoType} typ - The type to set for the rule
 */
func (v *TypeVisitor) promoteRuleType(ruleName string, typ RegoType) {
	existingType, exists := v.typeInfo.ruleTypes[ruleName]
	if !exists || v.isMorePrecise(typ, existingType) {
		v.typeInfo.ruleTypes[ruleName] = typ
	}
}

// processRuleHead analyzes the head of a rule and sets appropriate types
func (v *TypeVisitor) processRuleHead(ruleName string, head *ast.Head) {
	if head.Value == nil {
		return
	}

	if ref, ok := head.Value.Value.(ast.Ref); ok {
		headPath := v.buildRefPath(ref)
		v.typeInfo.varPaths[ruleName] = headPath
		if typ := v.inferRefType(ref); typ != TypeUnknown {
			v.promoteRuleType(ruleName, typ)
		}
	} else {
		// For direct value assignments in rule head
		typ := v.inferType(head.Value.Value)
		v.promoteRuleType(ruleName, typ)
	}
}

// processRuleBodyExpr processes a single expression in a rule body
func (v *TypeVisitor) processRuleBodyExpr(expr *ast.Expr, ruleName string) {
	v.VisitExpr(expr)

	// Only process assignments or equality expressions
	if !expr.IsAssignment() && !expr.IsEquality() {
		return
	}

	lhs := expr.Operand(0).Value
	rhs := expr.Operand(1).Value
	v.processRuleAssignment(lhs, rhs, ruleName)
}

// processRuleAssignment handles assignment expressions in rules
func (v *TypeVisitor) processRuleAssignment(lhs, rhs ast.Value, ruleName string) {
	lhsVar, isVar := lhs.(ast.Var)
	if !isVar {
		return
	}

	typ := v.inferType(rhs)
	if typ == TypeUnknown {
		return
	}

	// Handle direct rule assignment
	if string(lhsVar) == ruleName {
		v.promoteRuleType(ruleName, typ)
		return
	}

	// Handle indirect assignment
	v.promoteType(string(lhsVar), typ)
}

// processElseBranch processes the else branch of a rule
func (v *TypeVisitor) processElseBranch(elseBranch *ast.Rule) {
	if elseBranch == nil {
		return
	}

	elseVisitor := NewTypeVisitor()
	elseVisitor.typeInfo.InputSchema = v.typeInfo.InputSchema
	elseVisitor = elseVisitor.VisitRule(elseBranch)

	// Merge types from else branch
	for varName, typ := range elseVisitor.GetTypes() {
		v.promoteType(varName, typ)
	}
	for ruleName, typ := range elseVisitor.GetRuleTypes() {
		v.promoteRuleType(ruleName, typ)
	}
}

// VisitRule analyzes a single rule and returns the visitor used
func (v *TypeVisitor) VisitRule(rule *ast.Rule) *TypeVisitor {
	ruleName := rule.Head.Name.String()

	v.processRuleHead(ruleName, rule.Head)

	// Process rule body
	for _, expr := range rule.Body {
		v.processRuleBodyExpr(expr, ruleName)
	}

	v.processElseBranch(rule.Else)
	return v
}

/**
 * AnalyzeTypes performs complete type analysis on a Rego policy rule
 * @param {*ast.Rule} rule - The Rego rule to analyze
 * @return {map[string]RegoType} A map of variable names to their inferred types
 */
func AnalyzeTypes(rule *ast.Rule) *TypeVisitor {
	visitor := NewTypeVisitor()
	return visitor.VisitRule(rule)
}

// inferPrimitiveType handles primitive value type inference
func (v *TypeVisitor) inferPrimitiveType(val ast.Value) (RegoType, bool) {
	switch val.(type) {
	case ast.String:
		return TypeString, true
	case ast.Number:
		return TypeInt, true
	case ast.Boolean:
		return TypeBoolean, true
	case *ast.Array:
		return TypeArray, true
	case ast.Object:
		return TypeObject, true
	case ast.Set:
		return TypeSet, true
	default:
		return TypeUnknown, false
	}
}

// inferVarType handles variable type inference
func (v *TypeVisitor) inferVarType(varName string) (RegoType, bool) {
	// Check regular variable types
	if typ, exists := v.typeInfo.types[varName]; exists {
		return typ, true
	}
	// Check rule types
	if typ, exists := v.typeInfo.ruleTypes[varName]; exists {
		return typ, true
	}
	// Check stored path types
	if path, exists := v.typeInfo.varPaths[varName]; exists {
		if typ, exists := v.typeInfo.InputSchema.types[path]; exists {
			return typ, true
		}
	}
	return TypeUnknown, false
}

// inferType determines the type of a Rego value.
func (v *TypeVisitor) inferType(val ast.Value) RegoType {
	// Try primitive types first
	if typ, ok := v.inferPrimitiveType(val); ok {
		return typ
	}

	// Handle variables
	if varVal, ok := val.(ast.Var); ok {
		if typ, ok := v.inferVarType(string(varVal)); ok {
			return typ
		}
		return TypeUnknown
	}

	// Handle references
	if ref, ok := val.(ast.Ref); ok {
		return v.inferRefType(ref)
	}

	return TypeUnknown
}

// GetTypes returns the collected type information
func (v *TypeVisitor) GetTypes() map[string]RegoType {
	return v.typeInfo.types
}

// GetRuleTypes returns the collected rule type information
func (v *TypeVisitor) GetRuleTypes() map[string]RegoType {
	return v.typeInfo.ruleTypes
}

// GetTypeInfo returns the TypeInfo instance
func (v *TypeVisitor) GetTypeInfo() *TypeInfo {
	return v.typeInfo
}
