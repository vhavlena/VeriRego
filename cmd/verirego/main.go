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
func analyzeModule(mod *ast.Module, yamlFile string, params types.Parameters) {
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

	// Prepare input schema once
	inputSchema := types.NewInputSchema()
	if yamlFile != "" {
		yamlData, err := os.ReadFile(yamlFile)
		if err != nil {
			fmt.Printf("Warning: Failed to read YAML input file: %v\n", err)
		} else {
			if err := inputSchema.ProcessYAMLInput(yamlData); err != nil {
				fmt.Printf("Warning: Failed to process YAML input: %v\n", err)
			}
		}
	}

	// fmt.Printf("\nInput Schema %+v:\n", inputSchema)
	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema, params)
	typeAnalyzer.AnalyzeModule(compiledModule)

	typeMap := typeAnalyzer.GetAllTypes()
	if len(typeMap) > 0 {
		fmt.Printf("\nInferred Types (all rules):\n")
		for varName, varType := range typeMap {
			fmt.Printf("  %s: %s\n", varName, varType.PrettyPrintShort())
		}
	}
}

// analyzeRule performs analysis on a single Rego rule.
func analyzeRule(rule *ast.Rule, typeAnalyzer *types.TypeAnalyzer) {
	// Run type analysis using the shared type analyzer
	typeAnalyzer.AnalyzeRule(rule)

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
	specFile := flag.String("spec", "", "Path to the parameter specification file (optional)")

	// Parse flags
	flag.Parse()

	// Validate required arguments
	if *regoFile == "" {
		fmt.Println("Error: Rego policy file is required")
		fmt.Println("Usage:")
		flag.PrintDefaults()
		os.Exit(1)
	}

	var params types.Parameters
	if *specFile != "" {
		specData, err := os.ReadFile(*specFile)
		if err != nil {
			fmt.Printf("Warning: Failed to read spec file: %v\n", err)
		} else {
			params, err = types.FromSpecFile(specData)
			if err != nil {
				fmt.Printf("Warning: Failed to process spec file: %v\n", err)
			}
		}
	}

	module, err := parseRegoFile(*regoFile)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	analyzeModule(module, *yamlFile, params)
}
