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
		t.Fatalf("expected p to be 2, got: %v", num)
	}

	if pVal.Kind() != modelPkg.ValueInt {
		t.Fatalf("expected p to be int, got %s", pVal.Kind())
	}
}

// TestRunPolicyToModel_Function tests basic functionality of parametric rules.
// Since Rego is declarative, both forward and backward function definitions are tested (and also their equality).
func TestRunPolicyToModel_Function(t *testing.T) {
	validate := func(rego string) {
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
			t.Fatalf("expected p to be 2, got: %v", num)
		}

		if pVal.Kind() != modelPkg.ValueInt {
			t.Fatalf("expected p to be int, got %s", pVal.Kind())
		}
	}
	rego := `
package test

foo(x) = x + 1

p := foo(1)
`
	validate(rego)

	// function should not have to be forward declared
	rego = `
package test

p := foo(1)

foo(x) = x + 1
`
	validate(rego)
}

// TestRunPolicyToModel_ComplexFunction tests function with local variables and else branches
func TestRunPolicyToModel_ComplexFunction(t *testing.T) {
	rego := `
package test

default p := 1000

p := foo(2,-10)

foo(x,y) := x if {
	z := x*y
	z < x
} else := y
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
		t.Fatalf("expected p to be 2, got: %v", num)
	}

	if pVal.Kind() != modelPkg.ValueInt {
		t.Fatalf("expected p to be int, got %s", pVal.Kind())
	}
}

// TestRunPolicyToModel_ParseError verifies that parse errors are returned.
func TestRunPolicyToModel_ParseError(t *testing.T) {
	_, err := RunPolicyToModel("this is not rego", nil, nil)
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

// TestRef_E2E tests the full pipeline — parse → compile → inline → type-infer →
// SMT-translate → Z3 solve — for policies that access input and data fields
// through ast.Ref terms.  Each sub-test uses RunPolicyToModel so that Z3
// validates the generated SMT, exercising the complete ast.Ref code path.
func TestRef_E2E(t *testing.T) {
	t.Parallel()

	// allow if input.role == "admin": Z3 must satisfy the constraint with a
	// model where allow is present in the result.
	t.Run("InputStringRef", func(t *testing.T) {
		t.Parallel()
		rego := `
package example
allow if {
    input.role == "admin"
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}}}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// allow if input.count > 5: integer field comparison.
	t.Run("InputIntRef", func(t *testing.T) {
		t.Parallel()
		rego := `
package example
allow if {
    input.count > 5
}
`
		schema := []byte(`{"type":"object","properties":{"count":{"type":"integer"}}}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// allow if input.active == true: boolean field.
	t.Run("InputBooleanRef", func(t *testing.T) {
		t.Parallel()
		rego := `
package example
allow if {
    input.active == true
}
`
		schema := []byte(`{"type":"object","properties":{"active":{"type":"boolean"}}}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// Two input fields in one rule body.
	t.Run("MultipleInputRefs", func(t *testing.T) {
		t.Parallel()
		rego := `
package example
allow if {
    input.role == "admin"
    input.level > 0
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"},"level":{"type":"integer"}}}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// data.threshold: integer data-schema field compared with an input field.
	t.Run("DataRef", func(t *testing.T) {
		t.Parallel()
		rego := `
package example
allow if {
    input.count > data.threshold
}
`
		inputSchema := []byte(`{"type":"object","properties":{"count":{"type":"integer"}}}`)
		dataSchema := []byte(`{"type":"object","properties":{"threshold":{"type":"integer"}}}`)
		result, err := RunPolicyToModel(rego, inputSchema, dataSchema)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})
}
