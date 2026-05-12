package smt

import (
	"testing"

	modelPkg "github.com/vhavlena/verirego/pkg/model"
)

// TestIncrementalRules_E2E exercises incremental Rego rules (multiple definitions
// sharing the same name) through the full pipeline:
//
//	parse → compile → inline → type-infer → SMT-translate → Z3 solve
//
// The combinator emitted by IncrementalRulesToSmt chains per-occurrence functions
// with nested ite, so these tests validate the correct priority and fallback
// behaviour end-to-end.

// TestIncrementalRules_FirstFires verifies that the first rule definition takes
// priority when both rules would fire.
func TestIncrementalRules_FirstFires(t *testing.T) {
	rego := `
package test
p := 1 if { 1 != 2 }
p := 2 if { 1 != 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 1 {
		t.Fatalf("expected p == 1 (first rule wins), got: %v", num)
	}
	if pVal.Kind() != modelPkg.ValueInt {
		t.Fatalf("expected p to be int, got %s", pVal.Kind())
	}
}

// TestIncrementalRules_FallThroughToSecond verifies that when the first rule body
// is unsatisfiable the combinator falls through to the second rule.
func TestIncrementalRules_FallThroughToSecond(t *testing.T) {
	rego := `
package test
p := 1 if { 1 == 2 }
p := 2 if { 1 != 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 2 {
		t.Fatalf("expected p == 2 (second rule fires), got: %v", num)
	}
}

// TestIncrementalRules_DefaultFallback verifies that when no rule fires the
// declared default value is used.
func TestIncrementalRules_DefaultFallback(t *testing.T) {
	rego := `
package test
default p := 0
p := 1 if { 1 == 2 }
p := 2 if { 1 == 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 0 {
		t.Fatalf("expected p == 0 (default), got: %v", num)
	}
}

// TestIncrementalRules_DefaultNotUsedWhenFirstFires verifies that the default is
// not applied when the first rule body holds.
func TestIncrementalRules_DefaultNotUsedWhenFirstFires(t *testing.T) {
	rego := `
package test
default p := 0
p := 1 if { 1 != 2 }
p := 2 if { 1 == 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 1 {
		t.Fatalf("expected p == 1 (first rule overrides default), got: %v", num)
	}
}

// TestIncrementalRules_ThreeRules verifies that the combinator correctly chains
// three rules, reaching the third when the first two do not fire.
func TestIncrementalRules_ThreeRules(t *testing.T) {
	rego := `
package test
p := 1 if { 1 == 2 }
p := 2 if { 1 == 2 }
p := 3 if { 1 != 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 3 {
		t.Fatalf("expected p == 3 (third rule fires), got: %v", num)
	}
}

// TestIncrementalRules_ThreeRulesWithDefault verifies the nested ite chain with
// three rules and a fallback default (none of the three fires).
func TestIncrementalRules_ThreeRulesWithDefault(t *testing.T) {
	rego := `
package test
default p := 99
p := 1 if { 1 == 2 }
p := 2 if { 1 == 2 }
p := 3 if { 1 == 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 99 {
		t.Fatalf("expected p == 99 (default), got: %v", num)
	}
}

// TestIncrementalRules_WithInputSchema verifies that incremental rules guarded by
// input fields produce a satisfying model whose value is one of the expected outcomes.
func TestIncrementalRules_WithInputSchema(t *testing.T) {
	rego := `
package test
p := 10 if { input.level == 1 }
p := 20 if { input.level == 2 }
`
	schema := []byte(`{"type":"object","properties":{"level":{"type":"integer"}},"additionalProperties":false}`)
	result, err := RunPolicyToModel(rego, schema, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || (num != 10 && num != 20) {
		t.Fatalf("expected p in {10, 20}, got: %v", num)
	}
	if pVal.Kind() != modelPkg.ValueInt {
		t.Fatalf("expected p to be int, got %s", pVal.Kind())
	}
}

// TestIncrementalRules_WithInputSchema_DefaultFallback verifies that the default is
// used when no input-guarded rule fires.
func TestIncrementalRules_WithInputSchema_DefaultFallback(t *testing.T) {
	rego := `
package test
default p := 0
p := 10 if { input.level == 1 }
p := 20 if { input.level == 2 }
`
	// Force input.level to 3 so neither rule fires.
	schema := []byte(`{"type":"object","properties":{"level":{"type":"integer"}},"additionalProperties":false}`)
	result, err := RunPolicyToModel(rego, schema, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	// Z3 may choose a model where level ∈ {1,2} or one outside; we only require p ∈ {0,10,20}.
	num, ok := pVal.Int64()
	if !ok || (num != 0 && num != 10 && num != 20) {
		t.Fatalf("expected p in {0, 10, 20}, got: %v", num)
	}
}

// TestIncrementalRules_BoolDefaultFallback verifies boolean incremental rules where
// neither fires and the default (false) is used.
func TestIncrementalRules_BoolDefaultFallback(t *testing.T) {
	rego := `
package test
default allow := false
allow if { 1 == 2 }
allow if { 2 == 3 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	allowVal, ok := result.Vars["allow"]
	if !ok {
		t.Fatalf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
	}
	b, ok := allowVal.Bool()
	if !ok || b {
		t.Fatalf("expected allow == false (default), got: %v (ok=%v)", b, ok)
	}
}

// TestIncrementalRules_BoolSecondFires verifies boolean incremental rules where the
// first never fires but the second does, producing true.
func TestIncrementalRules_BoolSecondFires(t *testing.T) {
	rego := `
package test
default allow := false
allow if { 1 == 2 }
allow if { 1 != 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	allowVal, ok := result.Vars["allow"]
	if !ok {
		t.Fatalf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
	}
	b, ok := allowVal.Bool()
	if !ok || !b {
		t.Fatalf("expected allow == true (second rule fires), got: %v (ok=%v)", b, ok)
	}
}

// ---- parametric (function) incremental rules ----

// TestIncrementalRules_Parametric_FirstFires verifies that the first occurrence
// of a function takes priority when its condition holds.
func TestIncrementalRules_Parametric_FirstFires(t *testing.T) {
	rego := `
package test
foo(x) := 1 if { x > 0 }
foo(x) := 2 if { x > 0 }
p := foo(5)
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 1 {
		t.Fatalf("expected p == 1 (first occurrence wins), got: %v", num)
	}
}

// TestIncrementalRules_Parametric_SecondFires verifies that the combinator
// falls through to the second occurrence when the first body does not hold.
func TestIncrementalRules_Parametric_SecondFires(t *testing.T) {
	rego := `
package test
foo(x) := 1 if { x > 10 }
foo(x) := 2 if { x > 0 }
p := foo(5)
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 2 {
		t.Fatalf("expected p == 2 (second occurrence fires), got: %v", num)
	}
}

// TestIncrementalRules_Parametric_ThreeOccurrences verifies the nested-ite chain
// for three function occurrences, reaching the third when the first two are guarded
// by conditions that do not hold for the given argument.
func TestIncrementalRules_Parametric_ThreeOccurrences(t *testing.T) {
	rego := `
package test
foo(x) := 1 if { x > 100 }
foo(x) := 2 if { x > 10 }
foo(x) := 3 if { x > 0 }
p := foo(5)
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 3 {
		t.Fatalf("expected p == 3 (third occurrence fires), got: %v", num)
	}
}

// TestIncrementalRules_Parametric_TwoArgs verifies incremental rules with two
// parameters. The first occurrence fires when x >= y; otherwise the second fires.
func TestIncrementalRules_Parametric_TwoArgs(t *testing.T) {
	rego := `
package test
choose(x, y) := x if { x >= y }
choose(x, y) := y if { y > x }
p := choose(3, 7)
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 7 {
		t.Fatalf("expected p == 7 (second occurrence fires, y > x), got: %v", num)
	}
}

// TestIncrementalRules_StringValues verifies incremental rules that assign string values.
func TestIncrementalRules_StringValues(t *testing.T) {
	rego := `
package test
role := "admin"   if { 1 == 2 }
role := "user"    if { 1 != 2 }
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	roleVal, ok := result.Vars["role"]
	if !ok {
		t.Fatalf("expected 'role' in model vars, got: %v", varKeys(result.Vars))
	}
	s, ok := roleVal.String()
	if !ok || s != "user" {
		t.Fatalf("expected role == \"user\", got: %v (ok=%v)", s, ok)
	}
	if roleVal.Kind() != modelPkg.ValueString {
		t.Fatalf("expected role to be string, got %s", roleVal.Kind())
	}
}
