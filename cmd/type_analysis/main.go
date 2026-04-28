package main

import (
	"flag"
	"fmt"
	"os"
	"sort"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/types"
)

// newInputSchemaFromFlags builds an input schema from YAML examples or JSON Schema sources.
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

// analyzeModule compiles the Rego policy, optionally inlines helpers, and runs the type analyzer.
func analyzeModule(mod *ast.Module, yamlFile, jsonSchemaFile, dataYamlFile, dataJsonSchemaFile string, inline bool) {
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

	// Rename local variables to unique names before any simplification.
	renamer := simplify.NewLocalVarRenamer()
	compiledModule = renamer.SimplifyModule(compiledModule)

	if inline {
		inliner := simplify.NewInliner()
		inliner.GatherInlinePredicates(compiledModule)
		compiledModule = inliner.InlineModule(compiledModule)
	}

	compiledModule = types.RestoreEqualityOperators(mod, compiledModule)

	fmt.Printf("Compiled Module: %+v\n", compiledModule)
	fmt.Printf("\nRego Policy Analysis:\n")

	// Prepare input and data schemas (example-based or JSON Schema)
	inputSchema, err := newInputSchemaFromFlags(yamlFile, jsonSchemaFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: input schema: %v\n", err)
		return
	}
	dataSchema, err := newInputSchemaFromFlags(dataYamlFile, dataJsonSchemaFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: data schema: %v\n", err)
		return
	}
	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema)
	typeAnalyzer.DataSchema = dataSchema
	typeAnalyzer.AnalyzeModule(compiledModule)

	typeMap := typeAnalyzer.GetAllTypes()
	if len(typeMap) > 0 {
		fmt.Printf("\nInferred Types (all rules):\n")
		typeNames := make([]string, 0, len(typeMap))
		for name := range typeMap {
			typeNames = append(typeNames, name)
		}
		sort.Strings(typeNames)
		for _, varName := range typeNames {
			tp := typeMap[varName]
			fmt.Printf("  %s: %s\n", varName, tp.PrettyPrintShort())
		}
	}

	if len(compiledModule.Rules) > 0 {
		vc := typeAnalyzer.GetVarClassification()

		localVars := make([]string, 0, len(vc.Local))
		for v := range vc.Local {
			localVars = append(localVars, v)
		}
		sort.Strings(localVars)

		quantifiedVars := make([]string, 0, len(vc.Quantified))
		for v := range vc.Quantified {
			quantifiedVars = append(quantifiedVars, v)
		}
		sort.Strings(quantifiedVars)

		paramVars := make([]string, 0, len(vc.Parameter))
		for v := range vc.Parameter {
			paramVars = append(paramVars, v)
		}
		sort.Strings(paramVars)

		fmt.Printf("\nVariable Classification:\n")
		fmt.Printf("  parameters: %s\n", formatVarList(paramVars))
		fmt.Printf("  local:      %s\n", formatVarList(localVars))
		fmt.Printf("  quantified: %s\n", formatVarList(quantifiedVars))
	}
}

// formatVarList formats a sorted variable name slice for display.
func formatVarList(vars []string) string {
	if len(vars) == 0 {
		return "(none)"
	}
	return strings.Join(vars, ", ")
}

// parseRegoFile parses the provided Rego policy using the specified language version constraints.
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

// parseRegoVersionFlag normalizes CLI input to the ast.RegoVersion enum understood by OPA.
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
	inline := flag.Bool("inline", false, "Apply inlining to the module before type inference")

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

	analyzeModule(module, *yamlFile, *jsonSchemaFile, *dataYamlFile, *dataJsonSchemaFile, *inline)
}
