package main

import (
	// "fmt"
	"github.com/open-policy-agent/opa/ast"
)

// PropagatedValue represents a value that can be propagated through the AST during traversal.
// This interface provides methods for combining and creating values from AST terms, allowing
// for flexible value propagation strategies during AST analysis.
type PropagatedValue interface {
	// Join combines values from sibling nodes in the AST.
	// The method should be commutative and associative.
	Join(other PropagatedValue) PropagatedValue
	
	// FromBasicTerm creates a value from a basic term (leaf term or function call).
	// It extracts relevant information from the term for analysis.
	FromBasicTerm(term *ast.Term) PropagatedValue

	// FromPredicate(pred *ast.Expr) PropagatedValue
	
	// IsEmpty checks if the propagated value contains any meaningful information.
	IsEmpty() bool
}

// ASTVisitor defines an interface for traversing different types of AST nodes.
// Implementations can define specific behavior for each node type encountered
// during AST traversal.
type ASTVisitor interface {
	// VisitRule processes a Rule node and returns a PropagatedValue
	VisitRule(*ast.Rule) PropagatedValue
	// VisitExpr processes an expression node and returns a PropagatedValue
	VisitExpr(*ast.Expr) PropagatedValue
	// VisitHead processes a rule head node and returns a PropagatedValue
	VisitHead(*ast.Head) PropagatedValue
	// VisitTerm processes a term node and returns a PropagatedValue
	VisitTerm(*ast.Term) PropagatedValue
}

// ValueConstructor is a function type that creates new PropagatedValue instances.
// It's used to initialize new values during AST traversal.
type ValueConstructor func() PropagatedValue

// TraverseAST traverses an AST node using the provided visitor and value constructor.
// It determines the type of the node and delegates to the appropriate visitor method.
// Parameters:
//   - node: The AST node to traverse
//   - visitor: The visitor implementing node-specific processing logic
//   - constructor: A function to create new PropagatedValue instances
// Returns a PropagatedValue containing the combined results of the traversal
func TraverseAST(node interface{}, visitor ASTVisitor, constructor ValueConstructor) PropagatedValue {
	switch n := node.(type) {
	case *ast.Rule:
		return visitor.VisitRule(n)
	case *ast.Expr:
		return visitor.VisitExpr(n)
	case *ast.Head:
		return visitor.VisitHead(n)
	case *ast.Term:
		return visitor.VisitTerm(n)
	default:
		return constructor()
	}
}

// -----------------------------------------------------------

// ASTValueVisitor implements ASTVisitor to analyze and collect values during AST traversal.
// It maintains a PropagatedValue that accumulates information during the traversal.
type ASTValueVisitor struct {
	newValue PropagatedValue
}

// NewASTValueVisitor creates a new ASTValueVisitor initialized with a bottom value.
// The bottom value serves as the initial state for value propagation.
// Parameters:
//   - bottom: The initial PropagatedValue to use
func NewASTValueVisitor(bottom PropagatedValue) *ASTValueVisitor {
	return &ASTValueVisitor{
		newValue: bottom,
	}
}

// VisitRule processes a Rule node by combining values from its head and body.
// It recursively processes the rule's head, body expressions, and else clause if present.
// Parameters:
//   - rule: The Rule node to process
// Returns the combined PropagatedValue from all rule components
func (v *ASTValueVisitor) VisitRule(rule *ast.Rule) PropagatedValue {
	if rule == nil {
		return v.newValue
	}
	
	headValue := v.VisitHead(rule.Head)
	bodyValue := v.newValue
	
	for _, expr := range rule.Body {
		exprValue := v.VisitExpr(expr)
		bodyValue = bodyValue.Join(exprValue)
	}
	
	result := headValue.Join(bodyValue)
	if rule.Else != nil {
		elseValue := v.VisitRule(rule.Else)
		result = result.Join(elseValue)
	}
	
	return result
}

// VisitExpr processes an expression node by analyzing its structure and components.
// Handles different types of expressions including assignments, function calls,
// and expressions with 'with' modifiers.
// Parameters:
//   - expr: The expression node to process
// Returns the combined PropagatedValue from all expression components
func (v *ASTValueVisitor) VisitExpr(expr *ast.Expr) PropagatedValue {
	if expr == nil {
		return v.newValue
	}

	result := v.newValue

	// fmt.Printf("Debug: Visiting expression: %v\n", expr)
	
	if expr.IsAssignment() {
		op0 := v.VisitTerm(expr.Operand(0))
		op1 := v.VisitTerm(expr.Operand(1))
		result = result.Join(op0)
		result = result.Join(op1)
		return result
	}

	if expr.IsCall() {
		terms := expr.Terms.([]*ast.Term)
		// fmt.Printf("Debug: ----: %v\n", terms[0])

		// predicate name
		result = result.Join(result.FromBasicTerm(terms[0]))

		// Handle built-in functions
		// if len(terms) > 0 {
		// 	fmt.Printf("Debug: Found call expression with operator: %v\n", terms[0])
		// 	if op, ok := terms[0].Value.(ast.Var); ok {
		// 		result = result.Join(&StringOperations{
		// 			operations: []string{string(op)},
		// 		})
		// 	}
		// }
		// Handle the arguments
		for _, term := range terms[1:] {
			termValue := v.VisitTerm(term)
			result = result.Join(termValue)
		}
	}

	for _, with := range expr.With {
		withValue := v.VisitTerm(with.Value)
		result = result.Join(withValue)
	}

	return result
}

// VisitHead processes a rule head node by analyzing its value and key components.
// Parameters:
//   - head: The head node to process
// Returns the combined PropagatedValue from the head's components
func (v *ASTValueVisitor) VisitHead(head *ast.Head) PropagatedValue {
	if head == nil {
		return v.newValue
	}

	result := v.newValue
	
	if head.Value != nil {
		valueResult := v.VisitTerm(head.Value)
		result = result.Join(valueResult)
	}
	
	if head.Key != nil {
		keyResult := v.VisitTerm(head.Key)
		result = result.Join(keyResult)
	}

	return result
}

// VisitTerm processes a term node by analyzing its value based on its type.
// Handles various term types including basic values (String, Number, Boolean, Null),
// function calls, references, arrays, and objects.
// Parameters:
//   - term: The term node to process
// Returns the PropagatedValue derived from the term's contents
func (v *ASTValueVisitor) VisitTerm(term *ast.Term) PropagatedValue {
	if term == nil {
		return v.newValue
	}

	// fmt.Printf("Debug: Visiting term: %v\n", term)

	result := v.newValue
	
	switch val := term.Value.(type) {
	case ast.String, ast.Number, ast.Boolean, ast.Null:
		return result.FromBasicTerm(term)
	case ast.Var:
		// Handle built-in function names as variables
		return result.FromBasicTerm(term)
	case ast.Call:
		// For function calls, first handle the function name
		if len(val) > 0 {
			result = result.Join(result.FromBasicTerm(val[0]))
		}
		// Then process the arguments
		for _, t := range val {
			termValue := v.VisitTerm(t)
			result = result.Join(termValue)
		}
	case ast.Ref:
		for _, t := range val {
			termValue := v.VisitTerm(t)
			result = result.Join(termValue)
		}
	case *ast.Array:
		for i := 0; i < val.Len(); i++ {
			elemValue := v.VisitTerm(val.Elem(i))
			result = result.Join(elemValue)
		}
	case ast.Object:
		for _, k := range val.Keys() {
			keyValue := v.VisitTerm(k)
			valueValue := v.VisitTerm(val.Get(k))
			result = result.Join(keyValue)
			result = result.Join(valueValue)
		}
	}

	return result
}
