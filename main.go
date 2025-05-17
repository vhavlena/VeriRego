package main

import (
	"fmt"
	"os"
	"github.com/open-policy-agent/opa/ast"
)

// printRule analyzes and prints a Rego rule that contains string operations.
// It creates a new AST visitor to traverse the rule and identify string operations
// in the rule's conditions. If string operations are found (value is not empty),
// the rule is printed to standard output.
//
// Parameters:
//   - rule: The AST Rule node to analyze and potentially print
func printRule(rule *ast.Rule) {
	visitor := NewASTValueVisitor(NewStringOperations())
	val := TraverseAST(rule, visitor, func() PropagatedValue {
		return NewStringOperations()
	})
	if !val.IsEmpty() {
		fmt.Printf("%v\n", rule)
	}
}

// main is the entry point of the Rego analyzer program.
// It processes a Rego policy file specified as a command-line argument,
// parsing it into an AST and analyzing each rule for string operations.
// The program will exit with status code 1 if:
//   - No input file is specified
//   - The input file cannot be read
//   - The Rego module cannot be parsed
func main() {
	if len(os.Args) != 2 {
		fmt.Println("Usage: program <rego-file>")
		os.Exit(1)
	}

	// Read the Rego policy file
	regoFile := os.Args[1]
	content, err := os.ReadFile(regoFile)
	if err != nil {
		fmt.Printf("Error reading file: %v\n", err)
		os.Exit(1)
	}

	// Parse the module
	module, err := ast.ParseModule(regoFile, string(content))
	if err != nil {
		fmt.Printf("Error parsing module: %v\n", err)
		os.Exit(1)
	}

	for _, rule := range module.Rules {
		printRule(rule)
	}
}