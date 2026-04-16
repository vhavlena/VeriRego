package main

import (
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/smt"
	"github.com/vhavlena/verirego/pkg/types"
)

// newInputSchemaFromFlags loads either a YAML example or JSON schema input description.
// Returns an error when a file path is provided but cannot be read or parsed.
func newInputSchemaFromFlags(yamlFile, jsonSchemaFile string) (types.InputSchemaAPI, error) {
	// Default to example-based YAML/JSON input schema when provided.
	if yamlFile != "" {
		b, err := os.ReadFile(yamlFile)
		if err != nil {
			return nil, fmt.Errorf("failed to read input example file: %w", err)
		}
		is := types.NewInputSchema()
		if err := is.ProcessInput(b); err != nil {
			return nil, fmt.Errorf("failed to process input example: %w", err)
		}
		return is, nil
	}

	// Fallback to JSON Schema when provided.
	if jsonSchemaFile != "" {
		b, err := os.ReadFile(jsonSchemaFile)
		if err != nil {
			return nil, fmt.Errorf("failed to read JSON Schema file: %w", err)
		}
		js := types.NewInputJsonSchema()
		if err := js.ProcessInput(b); err != nil {
			return nil, fmt.Errorf("failed to process JSON Schema: %w", err)
		}
		return js, nil
	}

	// No schema information available.
	return nil, nil
}

// analyzeAndWriteSMT compiles, analyzes, and emits SMT-LIB for the provided module.
func analyzeAndWriteSMT(mod *ast.Module, yamlFile, jsonSchemaFile, dataYamlFile, dataJsonSchemaFile string, outFile string) error {
	// Compile the module
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{
		mod.Package.Path.String(): mod,
	})

	if compiler.Failed() {
		return fmt.Errorf("Compilation failed: %v", compiler.Errors)
	}

	compiledModule := compiler.Modules[mod.Package.Path.String()]

	// Rename local variables to unique names before any simplification.
	renamer := simplify.NewLocalVarRenamer()
	compiledModule = renamer.SimplifyModule(compiledModule)

	// Inline definitions before type analysis
	inliner := simplify.NewInliner()
	inliner.GatherInlinePredicates(compiledModule)
	compiledModule = inliner.InlineModule(compiledModule)

	// Prepare input and data schemas (example-based or JSON Schema)
	inputSchema, err := newInputSchemaFromFlags(yamlFile, jsonSchemaFile)
	if err != nil {
		return fmt.Errorf("input schema: %w", err)
	}
	dataSchema, err := newInputSchemaFromFlags(dataYamlFile, dataJsonSchemaFile)
	if err != nil {
		return fmt.Errorf("data schema: %w", err)
	}
	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema)
	typeAnalyzer.DataSchema = dataSchema
	typeAnalyzer.AnalyzeModule(compiledModule)

	// Prepare SMT translator
	translator := smt.NewTranslator(typeAnalyzer, compiledModule)
	if err := translator.GenerateSmtContent(); err != nil {
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

// parseRegoFile parses raw policy bytes using the selected Rego language version.
func parseRegoFile(file string, version ast.RegoVersion) (*ast.Module, error) {
	fileBytes, err := os.ReadFile(file)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %v", err)
	}

	module, err := ast.ParseModuleWithOpts(file, string(fileBytes), ast.ParserOptions{RegoVersion: version})
	if err != nil {
		return nil, fmt.Errorf("failed to parse module: %v", err)
	}

	return module, nil
}

// parseRegoVersionFlag converts user-friendly CLI input into an ast.RegoVersion value.
func parseRegoVersionFlag(value string) (ast.RegoVersion, error) {
	switch strings.ToLower(strings.TrimSpace(value)) {
	case "", "1", "1.x", "v1", "rego.v1":
		return ast.RegoV1, nil
	case "0", "0.x", "v0", "rego.v0":
		return ast.RegoV0, nil
	default:
		return ast.RegoUndefined, fmt.Errorf("invalid Rego version %q (expected 0 or 1)", value)
	}
}

func main() {
	// Define command line flags
	regoFile := flag.String("rego", "", "Path to the Rego policy file (required)")
	yamlFile := flag.String("yaml", "", "Path to the YAML input file (optional)")
	jsonSchemaFile := flag.String("json-schema", "", "Path to the JSON Schema file for input (optional)")
	dataYamlFile := flag.String("data-yaml", "", "Path to the YAML data file (optional)")
	dataJsonSchemaFile := flag.String("data-json-schema", "", "Path to the JSON Schema file for data (optional)")
	regoVersionFlag := flag.String("rego-version", "1", "Rego language version for parsing the policy (0 or 1)")
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

	regoVersion, err := parseRegoVersionFlag(*regoVersionFlag)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	module, err := parseRegoFile(*regoFile, regoVersion)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	err = analyzeAndWriteSMT(module, *yamlFile, *jsonSchemaFile, *dataYamlFile, *dataJsonSchemaFile, *outFile)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("SMT-LIB file written to %s\n", *outFile)
}
