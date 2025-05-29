package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/analysis"
	"github.com/vhavlena/verirego/pkg/types"
)

// analyzeModule performs analysis on a Rego module.
func analyzeModule(mod *ast.Module, yamlFile string) {
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
		analyzeRule(rule, yamlFile)
	}
}

// analyzeRule performs analysis on a single Rego rule.
func analyzeRule(rule *ast.Rule, yamlFile string) {
	fmt.Printf("\n=== Rule: %s ===\n", rule.Head.Name)

	// Create a type visitor
	visitor := types.NewTypeVisitor()

	// If YAML input file is provided, process it
	if yamlFile != "" {
		yamlData, err := os.ReadFile(yamlFile)
		if err != nil {
			fmt.Printf("Warning: Failed to read YAML input file: %v\n", err)
		} else {
			if err := visitor.GetTypeInfo().InputSchema.ProcessYAMLInput(yamlData); err != nil {
				fmt.Printf("Warning: Failed to process YAML input: %v\n", err)
			}
		}
	}

	// Perform detailed type analysis
	typeVisitor := types.AnalyzeTypes(rule)
	typeMap := typeVisitor.GetTypes()
	if len(typeMap) > 0 {
		fmt.Printf("\nInferred Types:\n")
		for varName, varType := range typeMap {
			fmt.Printf("  %s: %s\n", varName, varType)
		}
	}

	// Look for string operations
	opVisitor := analysis.NewASTValueVisitor(analysis.NewStringOperations())
	for _, expr := range rule.Body {
		opVisitor.VisitExpr(expr)
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
	// Define command line flags
	regoFile := flag.String("rego", "", "Path to the Rego policy file (required)")
	yamlFile := flag.String("yaml", "", "Path to the YAML input file (optional)")

	// Parse flags
	flag.Parse()

	// Validate required arguments
	if *regoFile == "" {
		fmt.Println("Error: Rego policy file is required")
		fmt.Println("Usage:")
		flag.PrintDefaults()
		os.Exit(1)
	}

	module, err := parseRegoFile(*regoFile)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	analyzeModule(module, *yamlFile)
}
