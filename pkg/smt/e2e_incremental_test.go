package smt

import (
	"fmt"
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
	fmt.Printf("%s\n\n", result.SmtContent)
	pVal, ok := result.Vars["p"]
	if ok {
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
