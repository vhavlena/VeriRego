package smt

import (
	"fmt"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	modelPkg "github.com/vhavlena/verirego/pkg/model"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/types"
	z3 "github.com/vhavlena/z3-go/z3"
)

// PolicyModel holds the satisfying model produced by running the full
// compile → type-inference → SMT-translation → Z3 pipeline.
type PolicyModel struct {
	// Vars maps each declared global SMT variable name to its model value.
	Vars map[string]modelPkg.Value
	// SmtContent is the raw SMT-LIB2 string generated for the policy,
	// intended for debugging and testing purposes.
	SmtContent string
}

// RunPolicyToModel is a test helper that executes the complete pipeline on a
// Rego policy string, mirroring the cmd/smt binary:
//
//  1. Parse the Rego source (Rego v1).
//  2. Compile with OPA's compiler.
//  3. Inline predicate definitions.
//  4. Infer types, optionally guided by a JSON Schema document.
//  5. Translate to SMT-LIB.
//  6. Assert the SMT-LIB in Z3 and check satisfiability.
//  7. Extract and return a model for all declared global variables.
//
// The returned PolicyModel includes the raw SMT-LIB2 string (SmtContent) for
// debugging and testing purposes, regardless of satisfiability.
//
// Parameters:
//
//	regoPolicy - Rego v1 policy source code (not a file path).
//	jsonSchema  - Raw JSON Schema bytes for input type inference; pass nil for no schema.
//
// Returns:
//
//	*PolicyModel - Satisfying model with variable values and SMT content (only when SAT).
//	error        - Non-nil on any pipeline failure or when the formula is UNSAT.
func RunPolicyToModel(regoPolicy string, jsonSchema []byte) (*PolicyModel, error) {
	// 1. Parse the Rego policy (Rego v1).
	mod, err := ast.ParseModuleWithOpts("policy.rego", regoPolicy, ast.ParserOptions{
		RegoVersion: ast.RegoV1,
	})
	if err != nil {
		return nil, fmt.Errorf("parse: %w", err)
	}

	// 2. Compile with OPA's compiler.
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{
		mod.Package.Path.String(): mod,
	})
	if compiler.Failed() {
		return nil, fmt.Errorf("compile: %v", compiler.Errors)
	}
	compiledModule := compiler.Modules[mod.Package.Path.String()]

	// 3. Inline predicate definitions.
	inliner := simplify.NewInliner()
	inliner.GatherInlinePredicates(compiledModule)
	compiledModule = inliner.InlineModule(compiledModule)

	// 4. Build input schema from the JSON Schema document.
	// GenerateSmtContent always declares input.review.object, which requires a
	// typed schema to generate constraints. Fall back to an empty object schema
	// when no JSON Schema is provided so the pipeline succeeds.
	inputSchema := types.InputSchemaAPI(types.NewInputJsonSchema())
	if len(jsonSchema) > 0 {
		js := types.NewInputJsonSchema()
		if err := js.ProcessInput(jsonSchema); err != nil {
			return nil, fmt.Errorf("json schema: %w", err)
		}
		inputSchema = js
	}

	// 5. Run type inference.
	var params types.Parameters
	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema, params)
	typeAnalyzer.AnalyzeModule(compiledModule)

	// 6. Generate SMT-LIB content.
	translator := NewTranslator(typeAnalyzer, compiledModule)
	if err := translator.GenerateSmtContent(); err != nil {
		return nil, fmt.Errorf("smt generation: %w", err)
	}
	smtContent := strings.Join(translator.SmtLines(), "\n")

	// 7. Assert the SMT-LIB in Z3 and check satisfiability.
	// smtContent is also stored in the returned PolicyModel for debugging.
	ctx := z3.NewContext(nil)
	defer ctx.Close()
	solver := ctx.NewSolver()
	defer solver.Close()

	if err := solver.AssertSMTLIB2String(smtContent); err != nil {
		return nil, fmt.Errorf("z3 assert: %w", err)
	}
	res, err := solver.Check()
	if err != nil {
		return nil, fmt.Errorf("z3 check: %w", err)
	}
	if res != z3.Sat {
		return nil, fmt.Errorf("formula is %v", res)
	}

	// 8. Extract model values for all declared global variables.
	z3Model := solver.Model()
	defer z3Model.Close()

	declaredVars := translator.getSmtVarsDeclare()
	vars := make(map[string]modelPkg.Value, len(declaredVars))
	for varName := range declaredVars {
		val, err := modelPkg.ValueFromModelVar(ctx, z3Model, varName)
		if err != nil {
			// The variable may be unconstrained or unavailable in the model; skip it.
			continue
		}
		vars[varName] = val
	}

	return &PolicyModel{Vars: vars, SmtContent: smtContent}, nil
}
