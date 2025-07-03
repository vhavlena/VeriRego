package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/smt"
	"github.com/vhavlena/verirego/pkg/types"
)

// analyzeAndWriteSMT performs type analysis and writes SMT-LIB output.
func analyzeAndWriteSMT(mod *ast.Module, yamlFile string, params types.Parameters, outFile string) error {
	// Compile the module
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{
		mod.Package.Path.String(): mod,
	})

	if compiler.Failed() {
		return fmt.Errorf("Compilation failed: %v", compiler.Errors)
	}

	compiledModule := compiler.Modules[mod.Package.Path.String()]

	// Inline definitions before type analysis
	inliner := simplify.NewInliner()
	inliner.GatherInlinePredicates(compiledModule)
	compiledModule = inliner.InlineModule(compiledModule)

	// Prepare input schema
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

	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema, params)
	typeAnalyzer.AnalyzeModule(compiledModule)

	// Prepare SMT translator
	translator := smt.NewTranslator(typeAnalyzer)
	if err := translator.GenerateTypeDefs(); err != nil {
		return fmt.Errorf("SMT generation failed: %v", err)
	}

	// Write SMT-LIB to file
	f, err := os.Create(outFile)
	if err != nil {
		return fmt.Errorf("Failed to create output file: %v", err)
	}
	defer f.Close()
	for _, line := range translator.SmtLines() {
		_, _ = f.WriteString(line + "\n")
	}
	return nil
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
	outFile := flag.String("out", "out.smt2", "Path to the output SMT-LIB file (default: out.smt2)")

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

	err = analyzeAndWriteSMT(module, *yamlFile, params, *outFile)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("SMT-LIB file written to %s\n", *outFile)
}
