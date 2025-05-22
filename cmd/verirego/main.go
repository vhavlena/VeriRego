package main

import (
	"fmt"
	"os"

	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/analysis"
	"github.com/vhavlena/verirego/pkg/types"
)

const (
	expectedArgCount = 2
)

// analyzeModule performs analysis on a Rego module.
func analyzeModule(mod *ast.Module) {
	// Compile the module
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{
		mod.Package.Path.String(): mod,
	})

	if compiler.Failed() {
		fmt.Printf("Compilation failed: %v\n", compiler.Errors)
		return
	}

	compiledModule := compiler.Modules[mod.Package.Path.String()]
	fmt.Printf("Compiled Module: %+v\n", compiledModule)
	fmt.Printf("\nRego Policy Analysis:\n")

	for _, rule := range compiledModule.Rules {
		analyzeRule(rule)
	}
}

// analyzeRule performs analysis on a single Rego rule.
func analyzeRule(rule *ast.Rule) {
	fmt.Printf("\n=== Rule: %s ===\n", rule.Head.Name)

	// Perform detailed type analysis
	tps := types.AnalyzeTypes(rule)
	if len(tps) > 0 {
		fmt.Printf("\nInferred Types:\n")
		for varName, varType := range tps {
			fmt.Printf("  %s: %s\n", varName, varType)
		}
	}

	// Look for string operations
	visitor := analysis.NewASTValueVisitor(analysis.NewStringOperations())
	for _, expr := range rule.Body {
		visitor.VisitExpr(expr)
	}
}

// parseRegoFile parses a Rego file and returns the AST Module.
func parseRegoFile(file string) (*ast.Module, error) {
	fileBytes, err := os.ReadFile(file)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %v", err)
	}

	module, err := ast.ParseModule(file, string(fileBytes))
	if err != nil {
		return nil, fmt.Errorf("failed to parse module: %v", err)
	}

	return module, nil
}

func main() {
	if len(os.Args) != expectedArgCount {
		fmt.Printf("Usage: %s <rego-file>\n", os.Args[0])
		os.Exit(1)
	}

	module, err := parseRegoFile(os.Args[1])
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	analyzeModule(module)
}
