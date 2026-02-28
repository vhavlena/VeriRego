package smt

import (
	"testing"

	modelPkg "github.com/vhavlena/verirego/pkg/model"
)

// TestRunPolicyToModel_Default verifies the full pipeline on a rule with a
// default value and a literal-only body. Neither rule is inlined away by the
// simplifier (GatherInlinePredicates only collects single-body boolean rules
// that return true).
func TestRunPolicyToModel_Default(t *testing.T) {
	rego := `
package test

default p := 2

p := 1 if {
	1 > 2
}
`
	result, err := RunPolicyToModel(rego, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 2 {
		t.Fatalf("expected p to be 2, got: %v", num)
	}

	if pVal.Kind() != modelPkg.ValueInt {
		t.Fatalf("expected p to be int, got %s", pVal.Kind())
	}
}

// TestRunPolicyToModel_ParseError verifies that parse errors are returned.
func TestRunPolicyToModel_ParseError(t *testing.T) {
	_, err := RunPolicyToModel("this is not rego", nil)
	if err == nil {
		t.Fatal("expected parse error, got nil")
	}
}

func varKeys(m map[string]modelPkg.Value) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	return keys
}
