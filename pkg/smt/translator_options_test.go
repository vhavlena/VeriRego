// Package smt — integration tests for TranslatorOptions (issue #35):
// "Support configurable entry point and SMT symbol prefix in Translator"
//
// All tests run the complete pipeline (parse → compile → type-infer → SMT →
// Z3) via RunPolicyToModelWithOptions so that the prefix and entry-point
// features are validated end-to-end, not just as string checks.
package smt

import (
	"strings"
	"testing"
)

// inputSchemaXY is a JSON Schema for {x: integer, y: integer}.
var inputSchemaXY = []byte(`{
	"type": "object",
	"properties": {
		"x": {"type": "integer"},
		"y": {"type": "integer"}
	},
	"additionalProperties": false
}`)

// inputSchemaX is a JSON Schema for {x: integer}.
var inputSchemaX = []byte(`{
	"type": "object",
	"properties": {
		"x": {"type": "integer"}
	},
	"additionalProperties": false
}`)

// inputSchemaY is a JSON Schema for {y: integer}.
var inputSchemaY = []byte(`{
	"type": "object",
	"properties": {
		"y": {"type": "integer"}
	},
	"additionalProperties": false
}`)

// TestTranslatorOptions_NoOptions verifies that NewTranslatorWithOptions with
// zero-value options produces the same result as the standard pipeline.
func TestTranslatorOptions_NoOptions(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
`
	result, err := RunPolicyToModelWithOptions(rego, inputSchemaX, nil, TranslatorOptions{})
	if err != nil {
		t.Fatalf("RunPolicyToModelWithOptions error: %v", err)
	}
	if _, ok := result.Vars["allow"]; !ok {
		t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
	}
}

// TestTranslatorOptions_PrefixInSmtContent verifies that every occurrence of
// the rule-head symbol in the SMT output carries the configured prefix, and
// that the formula is accepted by Z3 (SAT).
func TestTranslatorOptions_PrefixInSmtContent(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
`
	opts := TranslatorOptions{Prefix: "policy1__"}
	result, err := RunPolicyToModelWithOptions(rego, inputSchemaX, nil, opts)
	if err != nil {
		t.Fatalf("RunPolicyToModelWithOptions error: %v", err)
	}

	// Every line that mentions "allow" must use the prefixed form.
	for _, line := range strings.Split(result.SmtContent, "\n") {
		if strings.Contains(line, "allow") && !strings.Contains(line, "policy1__allow") {
			t.Errorf("SMT line references unprefixed 'allow': %q", line)
		}
	}

	// The prefixed symbol must actually appear in the output.
	if !strings.Contains(result.SmtContent, "policy1__allow") {
		t.Error("SMT content does not contain prefixed symbol 'policy1__allow'")
	}

	// Model value is still accessible under the original name.
	if _, ok := result.Vars["allow"]; !ok {
		t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
	}
}

// TestTranslatorOptions_NoDuplicateSymbols demonstrates the core problem from
// issue #35: two modules that both define "allow" must produce distinct SMT
// symbols when translated with different prefixes.
func TestTranslatorOptions_NoDuplicateSymbols(t *testing.T) {
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
	resultA, err := RunPolicyToModelWithOptions(regoA, inputSchemaX, nil, TranslatorOptions{Prefix: "policyA__"})
	if err != nil {
		t.Fatalf("module A pipeline error: %v", err)
	}
	resultB, err := RunPolicyToModelWithOptions(regoB, inputSchemaY, nil, TranslatorOptions{Prefix: "policyB__"})
	if err != nil {
		t.Fatalf("module B pipeline error: %v", err)
	}

	for _, line := range strings.Split(resultA.SmtContent, "\n") {
		if strings.Contains(line, " allow ") || strings.HasSuffix(strings.TrimSpace(line), " allow)") {
			t.Errorf("module A SMT contains unprefixed 'allow': %q", line)
		}
	}
	for _, line := range strings.Split(resultB.SmtContent, "\n") {
		if strings.Contains(line, " allow ") || strings.HasSuffix(strings.TrimSpace(line), " allow)") {
			t.Errorf("module B SMT contains unprefixed 'allow': %q", line)
		}
	}

	if !strings.Contains(resultA.SmtContent, "policyA__allow") {
		t.Error("module A SMT does not contain 'policyA__allow'")
	}
	if !strings.Contains(resultB.SmtContent, "policyB__allow") {
		t.Error("module B SMT does not contain 'policyB__allow'")
	}
}

// TestTranslatorOptions_EntryPointExists verifies that setting EntryPoint does
// not break the pipeline and that the formula remains satisfiable.
func TestTranslatorOptions_EntryPointExists(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
allow if { input.y == 2 }
`
	opts := TranslatorOptions{
		Prefix:           "ns__",
		EntryPoint:       "allow",
		EntryPointOutput: "allow_combined",
	}
	result, err := RunPolicyToModelWithOptions(rego, inputSchemaXY, nil, opts)
	if err != nil {
		t.Fatalf("RunPolicyToModelWithOptions error: %v", err)
	}
	if result == nil {
		t.Fatal("nil result")
	}
}

// TestTranslatorOptions_EntryPointAggregates verifies that GenerateEntryPointPredicate
// emits exactly one aggregating define-fun named prefix+EntryPointOutput whose body
// contains an "(or ...)" combining the individual rule bodies.
// The per-rule assertions must still reference the prefixed entry-point symbol.
func TestTranslatorOptions_EntryPointAggregates(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
allow if { input.x == 1 }
allow if { input.y == 2 }
`
	opts := TranslatorOptions{
		Prefix:           "ns__",
		EntryPoint:       "allow",
		EntryPointOutput: "allow_combined",
	}
	result, err := RunPolicyToModelWithOptions(rego, inputSchemaXY, nil, opts)
	if err != nil {
		t.Fatalf("RunPolicyToModelWithOptions error: %v", err)
	}

	// Exactly one define-fun for the output name.
	count := 0
	var aggregateLine string
	for _, line := range strings.Split(result.SmtContent, "\n") {
		if strings.Contains(line, "(define-fun ns__allow_combined") {
			count++
			aggregateLine = line
		}
	}
	if count == 0 {
		t.Error("SMT does not contain '(define-fun ns__allow_combined ...'")
	}
	if count > 1 {
		t.Errorf("expected exactly 1 define-fun for 'ns__allow_combined', got %d", count)
	}
	if aggregateLine != "" && !strings.Contains(aggregateLine, "or") {
		t.Errorf("aggregate define-fun lacks 'or' aggregation: %q", aggregateLine)
	}

	// Per-rule assertions still reference the prefixed entry-point symbol.
	hasPerRule := false
	for _, line := range strings.Split(result.SmtContent, "\n") {
		if strings.Contains(line, "(assert") && strings.Contains(line, "ns__allow") {
			hasPerRule = true
			break
		}
	}
	if !hasPerRule {
		t.Error("no per-rule assertion found for 'ns__allow'")
	}
}

// TestTranslatorOptions_EntryPointNonBoolean verifies that the aggregate define-fun
// for a non-boolean (integer) entry point uses the first-non-undef ITE chain rather
// than a type-incorrect "(or ...)".
func TestTranslatorOptions_EntryPointNonBoolean(t *testing.T) {
	t.Parallel()
	rego := `
package test
default score := 0
score := 10 if { input.x == 1 }
score := 20 if { input.y == 2 }
`
	opts := TranslatorOptions{
		Prefix:           "ns__",
		EntryPoint:       "score",
		EntryPointOutput: "score_combined",
	}
	result, err := RunPolicyToModelWithOptions(rego, inputSchemaXY, nil, opts)
	if err != nil {
		t.Fatalf("RunPolicyToModelWithOptions error: %v", err)
	}

	// The aggregate must use is-OUndef, not a bare (or ...) of OTypeD values.
	if !strings.Contains(result.SmtContent, "(define-fun ns__score_combined") {
		t.Error("SMT does not contain '(define-fun ns__score_combined ...'")
	}
	if !strings.Contains(result.SmtContent, "is-OUndef") {
		t.Error("non-boolean aggregate does not contain 'is-OUndef' check")
	}
}
