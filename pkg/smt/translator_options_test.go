// Package smt — failing tests for issue #35:
// "Support configurable entry point and SMT symbol prefix in Translator"
//
// These tests document the EXPECTED behavior once the feature is implemented.
// They currently fail because TranslatorOptions, NewTranslatorWithOptions, and
// GenerateEntryPointPredicate do not yet exist.
package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

// buildTranslatorWithOptions is a helper that parses a Rego module, creates a
// minimal TypeAnalyzer, and returns a Translator constructed with the given options.
func buildTranslatorWithOptions(t *testing.T, rego string, typeMap map[string]types.RegoTypeDef, opts TranslatorOptions) *Translator {
	t.Helper()
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types: typeMap,
		Refs:  map[string]ast.Value{},
	}
	return NewTranslatorWithOptions(ta, mod, opts)
}

// TestNewTranslatorWithOptions_Exists verifies that TranslatorOptions and
// NewTranslatorWithOptions are defined and that the returned Translator is non-nil.
func TestNewTranslatorWithOptions_Exists(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
`
	typeMap := map[string]types.RegoTypeDef{
		"allow": types.NewAtomicType(types.AtomicBoolean),
		"input": types.NewObjectType(map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
		}),
	}
	opts := TranslatorOptions{
		Prefix:     "policy1__",
		EntryPoint: "allow",
	}
	tr := buildTranslatorWithOptions(t, rego, typeMap, opts)
	if tr == nil {
		t.Fatal("NewTranslatorWithOptions returned nil")
	}
}

// TestPrefix_AppliedToAssertions verifies that every SMT assertion emitted for a
// rule whose head name is "allow" uses the prefixed symbol "policy1__allow" when
// the Prefix option is set.
func TestPrefix_AppliedToAssertions(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
`
	typeMap := map[string]types.RegoTypeDef{
		"allow": types.NewAtomicType(types.AtomicBoolean),
		"input": types.NewObjectType(map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
		}),
	}
	opts := TranslatorOptions{Prefix: "policy1__"}
	tr := buildTranslatorWithOptions(t, rego, typeMap, opts)

	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}

	lines := tr.SmtLines()
	if len(lines) == 0 {
		t.Fatal("no SMT lines generated")
	}

	for _, line := range lines {
		if strings.Contains(line, "allow") && !strings.Contains(line, "policy1__allow") {
			t.Errorf("SMT line contains unprefixed symbol 'allow': %q", line)
		}
	}

	found := false
	for _, line := range lines {
		if strings.Contains(line, "policy1__allow") {
			found = true
			break
		}
	}
	if !found {
		t.Error("no SMT line contains the prefixed symbol 'policy1__allow'")
	}
}

// TestPrefix_NoDuplicateSymbols demonstrates the concrete problem described in
// the issue: two modules that both define "allow" must produce distinct SMT symbols
// when each is translated with a unique prefix.
func TestPrefix_NoDuplicateSymbols(t *testing.T) {
	t.Parallel()
	regoA := `
package a
default allow := false
allow if { input.x == 1 }
`
	regoB := `
package b
default allow := false
allow if { input.y == 2 }
`
	typeMap := map[string]types.RegoTypeDef{
		"allow": types.NewAtomicType(types.AtomicBoolean),
		"input": types.NewObjectType(map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
			"y": types.NewAtomicType(types.AtomicInt),
		}),
	}

	modA, err := ast.ParseModule("a.rego", regoA)
	if err != nil {
		t.Fatalf("failed to parse module A: %v", err)
	}
	modB, err := ast.ParseModule("b.rego", regoB)
	if err != nil {
		t.Fatalf("failed to parse module B: %v", err)
	}

	taA := &types.TypeAnalyzer{Types: typeMap, Refs: map[string]ast.Value{}}
	taB := &types.TypeAnalyzer{Types: typeMap, Refs: map[string]ast.Value{}}

	trA := NewTranslatorWithOptions(taA, modA, TranslatorOptions{Prefix: "policyA__"})
	trB := NewTranslatorWithOptions(taB, modB, TranslatorOptions{Prefix: "policyB__"})

	if err := trA.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt A error: %v", err)
	}
	if err := trB.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt B error: %v", err)
	}

	combined := append(trA.SmtLines(), trB.SmtLines()...)

	// Ensure neither raw "allow" nor duplicate define-fun symbols appear.
	for _, line := range combined {
		if strings.Contains(line, " allow ") || strings.HasSuffix(line, " allow)") {
			t.Errorf("combined SMT contains unprefixed 'allow' symbol: %q", line)
		}
	}

	// Both prefixed symbols must be present.
	hasA, hasB := false, false
	for _, line := range combined {
		if strings.Contains(line, "policyA__allow") {
			hasA = true
		}
		if strings.Contains(line, "policyB__allow") {
			hasB = true
		}
	}
	if !hasA {
		t.Error("combined SMT does not contain 'policyA__allow'")
	}
	if !hasB {
		t.Error("combined SMT does not contain 'policyB__allow'")
	}
}

// TestGenerateEntryPointPredicate_Exists verifies that GenerateEntryPointPredicate
// is callable and does not return an error when the entry point is a known rule.
func TestGenerateEntryPointPredicate_Exists(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
allow if { input.y == 2 }
`
	typeMap := map[string]types.RegoTypeDef{
		"allow": types.NewAtomicType(types.AtomicBoolean),
		"input": types.NewObjectType(map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
			"y": types.NewAtomicType(types.AtomicInt),
		}),
	}
	opts := TranslatorOptions{EntryPoint: "allow"}
	tr := buildTranslatorWithOptions(t, rego, typeMap, opts)

	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	if err := tr.GenerateEntryPointPredicate(); err != nil {
		t.Fatalf("GenerateEntryPointPredicate error: %v", err)
	}
}

// TestGenerateEntryPointPredicate_EmitsAggregateFun verifies that
// GenerateEntryPointPredicate emits a define-fun whose name equals EntryPointOutput
// (with prefix) and whose body aggregates the individual rule predicates with an
// "(or ...)" expression, using a fresh name that does not clash with per-rule assertions.
func TestGenerateEntryPointPredicate_EmitsAggregateFun(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
allow if { input.y == 2 }
`
	typeMap := map[string]types.RegoTypeDef{
		"allow": types.NewAtomicType(types.AtomicBoolean),
		"input": types.NewObjectType(map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
			"y": types.NewAtomicType(types.AtomicInt),
		}),
	}
	opts := TranslatorOptions{
		Prefix:           "ns__",
		EntryPoint:       "allow",
		EntryPointOutput: "allow_combined",
	}
	tr := buildTranslatorWithOptions(t, rego, typeMap, opts)

	if err := tr.TranslateModuleToSmt(); err != nil {
		t.Fatalf("TranslateModuleToSmt error: %v", err)
	}
	if err := tr.GenerateEntryPointPredicate(); err != nil {
		t.Fatalf("GenerateEntryPointPredicate error: %v", err)
	}

	lines := tr.SmtLines()

	// The aggregate define-fun must use the fresh output name, not the per-rule name.
	count := 0
	var aggregateLine string
	for _, line := range lines {
		if strings.Contains(line, "(define-fun ns__allow_combined") {
			count++
			aggregateLine = line
		}
	}
	if count == 0 {
		t.Error("GenerateEntryPointPredicate did not emit '(define-fun ns__allow_combined ...'")
	}
	if count > 1 {
		t.Errorf("GenerateEntryPointPredicate emitted %d define-fun lines for 'ns__allow_combined', expected 1", count)
	}
	if aggregateLine != "" && !strings.Contains(aggregateLine, "or") {
		t.Errorf("aggregate define-fun does not contain 'or' aggregation: %q", aggregateLine)
	}

	// Per-rule assertions must still use the prefixed entry-point name, not the output name.
	hasPerRuleAssert := false
	for _, line := range lines {
		if strings.Contains(line, "(assert") && strings.Contains(line, "ns__allow") {
			hasPerRuleAssert = true
			break
		}
	}
	if !hasPerRuleAssert {
		t.Error("no per-rule assertion found for 'ns__allow'")
	}
}

// TestGenerateSmtContent_WithOptions verifies that GenerateSmtContent respects the
// prefix and entry-point options and completes without error.
func TestGenerateSmtContent_WithOptions(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { true }
`
	mod, err := ast.ParseModule("test.rego", rego)
	if err != nil {
		t.Fatalf("failed to parse rego: %v", err)
	}

	ta := types.NewTypeAnalyzerWithParams(mod.Package.Path, types.NewInputSchema())
	ta.AnalyzeModule(mod)

	opts := TranslatorOptions{
		Prefix:     "pfx__",
		EntryPoint: "allow",
	}
	tr := NewTranslatorWithOptions(ta, mod, opts)
	if err := tr.GenerateSmtContent(); err != nil {
		t.Fatalf("GenerateSmtContent error: %v", err)
	}

	lines := tr.SmtLines()
	found := false
	for _, line := range lines {
		if strings.Contains(line, "pfx__allow") {
			found = true
			break
		}
	}
	if !found {
		t.Error("GenerateSmtContent output does not contain prefixed symbol 'pfx__allow'")
	}
}
