// Package types provides type analysis for Rego AST.
package types

import (
	"github.com/open-policy-agent/opa/ast"
)

// TypeAnalyzer performs type analysis on Rego AST
type TypeAnalyzer struct {
	types      map[string]RegoTypeDef // Store types by string key
	refs       map[string]ast.Value   // Map string keys back to original values
	schema     *InputSchema
	parameters Parameters
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
func NewTypeAnalyzer(schema *InputSchema) *TypeAnalyzer {
	return &TypeAnalyzer{
		types:  make(map[string]RegoTypeDef),
		refs:   make(map[string]ast.Value),
		schema: schema,
	}
}

// NewTypeAnalyzerWithParams creates a new type analyzer with parameters.
//
// Parameters:
//
//	schema *InputSchema: The input schema to use for type inference.
//	params Parameters: The parameters for the type analyzer.
//
// Returns:
//
//	*TypeAnalyzer: A new instance of TypeAnalyzer with parameters.
func NewTypeAnalyzerWithParams(schema *InputSchema, params Parameters) *TypeAnalyzer {
	return &TypeAnalyzer{
		types:      make(map[string]RegoTypeDef),
		refs:       make(map[string]ast.Value),
		schema:     schema,
		parameters: params,
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
	if typ, exists := ta.types[key]; exists {
		return typ
	}
	return ta.inferType(val)
}

// setType sets the type for a value only if the new type is more precise than the existing one
//
// Parameters:
//
//	val ast.Value: The AST value to set the type for.
//	typ RegoTypeDef: The type to assign to the value.
func (ta *TypeAnalyzer) setType(val ast.Value, typ RegoTypeDef) {
	key := ta.getValueKey(val)
	if existingType, exists := ta.types[key]; exists {
		// Only update if new type is more precise
		if !typ.IsMorePrecise(&existingType) {
			return
		}
	}
	ta.types[key] = typ
	ta.refs[key] = val
}

// InferTermType infers the type of an AST term by analyzing its value.
//
// Parameters:
//
//	term *ast.Term: The AST term to infer the type for.
//
// Returns:
//
//	RegoTypeDef: The inferred type of the term.
func (ta *TypeAnalyzer) InferTermType(term *ast.Term) RegoTypeDef {
	if term == nil {
		return NewUnknownType()
	}
	return ta.inferType(term.Value)
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

	term, ok := expr.Terms.(*ast.Term)
	if ok {
		// If the expression is a single term, infer its type directly
		return ta.InferTermType(term)
	}

	// Handle different expression types based on Terms
	terms, ok := expr.Terms.([]*ast.Term)
	// fmt.Printf("Expression terms: %v %v\n", terms, ok)
	if !ok || len(terms) == 0 {
		return NewUnknownType()
	}

	// For simple expressions with a single term
	if len(terms) == 1 {
		return ta.InferTermType(terms[0])
	}

	// Handle built-in operators and functions
	if expr.IsCall() {
		operator := terms[0]
		switch {
		case isStringFunction(operator.String()):
			return NewAtomicType(AtomicString)
		case isNumericFunction(operator.String()):
			return NewAtomicType(AtomicInt)
		case isBooleanFunction(operator.String()):
			return NewAtomicType(AtomicBoolean)
		case isEquality(operator.String()):
			typeLeft := ta.InferTermType(terms[1])
			typeRight := ta.InferTermType(terms[2])
			ta.setType(terms[1].Value, typeLeft)
			ta.setType(terms[1].Value, typeRight)
			ta.setType(terms[2].Value, typeRight)
			ta.setType(terms[2].Value, typeLeft)
		}
	}

	// For comparison operators, return boolean type
	if expr.Operator() != nil {
		return NewAtomicType(AtomicBoolean)
	}

	// For all other cases, infer type from the first term
	return ta.InferTermType(terms[0])
}

// inferType infers the type of an AST value.
//
// Parameters:
//
//	val ast.Value: The AST value to infer the type for.
//
// Returns:
//
//	RegoTypeDef: The inferred type of the value.
func (ta *TypeAnalyzer) inferType(val ast.Value) RegoTypeDef {
	if val == nil {
		return NewUnknownType()
	}

	// Use GetType to check for existing type (caching)
	key := ta.getValueKey(val)
	if typ, exists := ta.types[key]; exists {
		return typ
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
			elemType := ta.GetType(v.Elem(0).Value)
			typ = NewArrayType(elemType)
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
	case ast.Var:
		if t, exists := ta.types[ta.getValueKey(v)]; exists {
			typ = t
		} else {
			typ = NewUnknownType()
		}
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
	if head == "input" {
		// Check for input.parameters.<name>
		if len(ref) >= 3 {
			second := ref[1].Value.String()
			if second == "\"parameters\"" {
				// Only support input.parameters.<name> (not nested)
				if str, ok := ref[2].Value.(ast.String); ok {
					// fmt.Printf("Parameter name: %s\n", str)
					name := string(str)
					if param, exists := ta.parameters[name]; exists {
						return param.dt
					}
				}
			}
		}
		// Fallback to schema for other input references
		path := make([]string, 0, len(ref)-1)
		for _, term := range ref[1:] {
			if str, ok := term.Value.(ast.String); ok {
				path = append(path, string(str))
			}
		}
		if typ, exists := ta.schema.GetType(path); exists && typ != nil {
			return *typ
		}
	}
	return NewUnknownType()
}

// AnalyzeRule performs type analysis on a Rego rule.
//
// Parameters:
//
//	rule *ast.Rule: The Rego rule to analyze.
func (ta *TypeAnalyzer) AnalyzeRule(rule *ast.Rule) {
	// Analyze rule head value if it exists
	if rule.Head.Value != nil {
		ta.inferType(rule.Head.Value.Value)
	}

	// Analyze rule body
	for _, expr := range rule.Body {
		ta.InferExprType(expr)
	}
}

// GetAllTypes returns a copy of all inferred variable types.
//
// Returns:
//
//	map[string]RegoTypeDef: A map of variable names to their inferred types.
func (ta *TypeAnalyzer) GetAllTypes() map[string]RegoTypeDef {
	result := make(map[string]RegoTypeDef, len(ta.types))
	for k, v := range ta.types {
		result[k] = v
	}
	return result
}

// isStringFunction checks if a function name corresponds to a string operation.
//
// Parameters:
//
//	name string: The function name to check.
//
// Returns:
//
//	bool: True if the function is a string operation, false otherwise.
func isStringFunction(name string) bool {
	stringOps := map[string]bool{
		"trim": true, "replace": true, "concat": true,
		"format": true, "lower": true, "upper": true,
		"split": true,
	}
	return stringOps[name]
}

// isNumericFunction checks if a function name corresponds to a numeric operation.
//
// Parameters:
//
//	name string: The function name to check.
//
// Returns:
//
//	bool: True if the function is a numeric operation, false otherwise.
func isNumericFunction(name string) bool {
	numericOps := map[string]bool{
		"plus": true, "minus": true, "mul": true,
		"div": true,
	}
	return numericOps[name]
}

// isBooleanFunction checks if a function name corresponds to a boolean operation.
//
// Parameters:
//
//	name string: The function name to check.
//
// Returns:
//
//	bool: True if the function is a boolean operation, false otherwise.
func isBooleanFunction(name string) bool {
	booleanOps := map[string]bool{
		"neq": true, "and": true,
		"or": true, "not": true,
		"lt": true, "contains": true,
		"startswith": true, "endswith": true,
	}
	return booleanOps[name]
}

// isEquality checks if a function name corresponds to an equality operation.
//
// Parameters:
//
//	name string: The function name to check.
//
// Returns:
//
//	bool: True if the function is an equality operation, false otherwise.
func isEquality(name string) bool {
	equalityOps := map[string]bool{
		"eq": true, "assign": true,
	}
	return equalityOps[name]
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
func AnalyzeTypes(rule *ast.Rule, schema *InputSchema, params Parameters) *TypeAnalyzer {
	analyzer := NewTypeAnalyzerWithParams(schema, params)
	analyzer.AnalyzeRule(rule)
	return analyzer
}
