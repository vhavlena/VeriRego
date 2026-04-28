// schema_inference derives a JSON Schema for the input and data documents expected
// by a Rego policy without requiring any example input or hand-written schema.
//
// The tool compiles the policy, walks the AST, and infers types for every
// input.* and data.* reference from context:
//   - Equality/assignment with a literal → the literal's type
//   - Numeric comparison operators (gt, lt, …) → integer
//   - Known string builtins (startswith, concat, …) → string
//   - Iterated with [_] → array
//   - Field access → object
//
// The inferred schemas are written as JSON Schema (Draft-07) documents.
package main

import (
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/infer"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/types"
)

func main() {
	regoFile := flag.String("rego", "", "Path to the Rego policy file (required)")
	outInput := flag.String("out-input", "", "Output file for the inferred input JSON Schema (default: stdout)")
	outData := flag.String("out-data", "", "Output file for the inferred data JSON Schema (default: stdout)")
	regoVersionFlag := flag.String("rego-version", "1", "Rego language version (0 or 1)")
	inlineFlag := flag.Bool("inline", false, "Apply predicate inlining before inference")

	flag.Parse()

	if *regoFile == "" {
		fmt.Fprintln(os.Stderr, "Error: -rego is required")
		flag.PrintDefaults()
		os.Exit(1)
	}

	regoVersion, err := parseRegoVersionFlag(*regoVersionFlag)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	mod, err := parseRegoFile(*regoFile, regoVersion)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Compile the module so that operator names and refs are in canonical form.
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{mod.Package.Path.String(): mod})
	if compiler.Failed() {
		fmt.Fprintf(os.Stderr, "Compilation failed: %v\n", compiler.Errors)
		os.Exit(1)
	}

	compiled := compiler.Modules[mod.Package.Path.String()]

	if *inlineFlag {
		inliner := simplify.NewInliner()
		inliner.GatherInlinePredicates(compiled)
		compiled = inliner.InlineModule(compiled)
	}

	compiled = types.RestoreEqualityOperators(mod, compiled)

	// Run schema inference.
	inferrer := infer.New()
	inferrer.InferFromModule(compiled, mod.Package.Path)

	// Serialize and write the input schema.
	inputSchema := infer.ToJSONSchema(inferrer.Input, true)
	inputJSON, err := inputSchema.MarshalIndent()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to serialize input schema: %v\n", err)
		os.Exit(1)
	}

	// Serialize and write the data schema.
	dataSchema := infer.ToJSONSchema(inferrer.Data, true)
	dataJSON, err := dataSchema.MarshalIndent()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to serialize data schema: %v\n", err)
		os.Exit(1)
	}

	if err := writeOutput(*outInput, "input", inputJSON); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing input schema: %v\n", err)
		os.Exit(1)
	}
	if err := writeOutput(*outData, "data", dataJSON); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing data schema: %v\n", err)
		os.Exit(1)
	}
}

// writeOutput writes bytes to a file (when path is non-empty) or to stdout
// with a labelled header.
func writeOutput(path, label string, data []byte) error {
	if path == "" {
		fmt.Printf("=== %s schema ===\n", label)
		fmt.Println(string(data))
		return nil
	}
	if err := os.WriteFile(path, data, 0o644); err != nil {
		return err
	}
	fmt.Printf("Written %s schema to %s\n", label, path)
	return nil
}

func parseRegoFile(file string, version ast.RegoVersion) (*ast.Module, error) {
	b, err := os.ReadFile(file)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %w", err)
	}
	mod, err := ast.ParseModuleWithOpts(file, string(b), ast.ParserOptions{RegoVersion: version})
	if err != nil {
		return nil, fmt.Errorf("failed to parse module: %w", err)
	}
	return mod, nil
}

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
