// Package types provides type analysis for Rego AST.
package types

import (
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
	types map[string]RegoType
}

/**
 * NewTypeInfo creates a new TypeInfo instance and returns a new initialized TypeInfo with an empty types map.
 * @return {*TypeInfo} A new initialized TypeInfo with an empty types map
 */
func NewTypeInfo() *TypeInfo {
	return &TypeInfo{
		types: make(map[string]RegoType),
	}
}

// TypeVisitor implements type analysis for Rego AST.
type TypeVisitor struct {
	typeInfo *TypeInfo
}

/**
 * NewTypeVisitor creates a new TypeVisitor.
 * @return {*TypeVisitor} A new TypeVisitor instance initialized with an empty TypeInfo
 */
func NewTypeVisitor() *TypeVisitor {
	return &TypeVisitor{
		typeInfo: NewTypeInfo(),
	}
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
	// Get the RHS value type
	valueType := v.inferType(expr.Operand(1).Value)

	// Handle LHS variable
	if variable, ok := expr.Operand(0).Value.(ast.Var); ok {
		v.promoteType(string(variable), valueType)
	}
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
			v.updateVariableType(varName, variable)
		}
	}
}

/**
 * updateVariableType updates the type of a variable if needed.
 * Only updates if the variable has no type or is currently unknown.
 * @param {string} varName - The name of the variable to update
 * @param {ast.Value} value - The value to infer the type from
 */
func (v *TypeVisitor) updateVariableType(varName string, value ast.Value) {
	existingType, exists := v.typeInfo.types[varName]
	if !exists || existingType == TypeUnknown {
		if newType := v.inferType(value); newType != TypeUnknown {
			v.typeInfo.types[varName] = newType
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
		"sprintf":    true,
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

	// Common reference patterns
	head := ref[0].Value.String()
	switch head {
	case "input":
		return v.inferInputRefType(ref[1:])
	case "data":
		return v.inferDataRefType(ref[1:])
	}

	return TypeUnknown
}

/**
 * inferInputRefType infers types for input.* references.
 * @param {ast.Ref} ref - The reference path to analyze
 * @return {RegoType} The inferred type of the reference
 */
func (v *TypeVisitor) inferInputRefType(ref ast.Ref) RegoType {
	if len(ref) == 0 {
		return TypeObject
	}

	for _, term := range ref {
		if variable, ok := term.Value.(ast.Var); ok {
			v.promoteType(variable.String(), TypeIndex)
		}
	}

	return TypeObject
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
 * inferType determines the type of a Rego value.
 * It handles all basic Rego types including strings, numbers, booleans, arrays, objects, and references.
 * @param {ast.Value} val - The value to analyze
 * @return {RegoType} The inferred type of the value
 */
func (v *TypeVisitor) inferType(val ast.Value) RegoType {
	switch val := val.(type) {
	case ast.String:
		return TypeString
	case ast.Number:
		return TypeInt
	case ast.Boolean:
		return TypeBoolean
	case *ast.Array:
		return TypeArray
	case ast.Object:
		return TypeObject
	case ast.Set:
		return TypeSet
	case ast.Ref:
		return v.inferRefType(val)
	default:
		return TypeUnknown
	}
}

/**
 * GetTypes returns the collected type information.
 * @return {map[string]RegoType} A map of variable names to their inferred types
 */
func (v *TypeVisitor) GetTypes() map[string]RegoType {
	return v.typeInfo.types
}

/**
 * AnalyzeTypes performs complete type analysis on a Rego policy rule.
 * It analyzes both the rule head and body to infer types of all variables.
 * @param {*ast.Rule} rule - The Rego rule to analyze
 * @return {map[string]RegoType} A map of variable names to their inferred types
 */
func AnalyzeTypes(rule *ast.Rule) map[string]RegoType {
	visitor := NewTypeVisitor()

	// Analyze rule head
	if rule.Head.Key != nil {
		if v, ok := rule.Head.Key.Value.(ast.Var); ok {
			visitor.promoteType(string(v), visitor.inferType(rule.Head.Key.Value))
		}
	}

	// Process rule body
	for _, expr := range rule.Body {
		visitor.VisitExpr(expr)
	}

	return visitor.GetTypes()
}
