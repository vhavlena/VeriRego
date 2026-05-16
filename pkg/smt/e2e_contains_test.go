package smt

import (
	"strings"
	"testing"

	modelPkg "github.com/vhavlena/verirego/pkg/model"
)

// TestContains_E2E runs end-to-end tests for the `contains` (partial-set) rule syntax.
// Each contains rule `name contains v if { body }` is translated as a predicate
// function `name(v) -> OTypeBoolean` that returns (OBoolean true) when the body holds.
func TestContains_E2E(t *testing.T) {
	t.Parallel()

	// A single contains rule where the key is assigned in the body.
	// The generated define-fun should appear in the SMT output.
	t.Run("SingleContainsRule_SmtOutput", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

my_rule contains v if {
    v := input.role
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if !strings.Contains(result.SmtContent, "define-fun my_rule") {
			t.Errorf("expected define-fun for my_rule in SMT output:\n%s", result.SmtContent)
		}
	})

	// Contains rule where the key comes from an input field.
	// The predicate captures: allowed_roles(v) iff v equals input.role.
	t.Run("ContainsFromInputField", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

allowed_roles contains v if {
    v := input.role
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if !strings.Contains(result.SmtContent, "define-fun allowed_roles") {
			t.Errorf("expected define-fun for allowed_roles in SMT output:\n%s", result.SmtContent)
		}
	})

	// Multiple incremental contains rules sharing the same name are combined into
	// a single predicate function using nested ite via IncrementalRulesToSmt.
	t.Run("IncrementalContainsRules_SmtOutput", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

roles contains v if {
    v := input.role1
}

roles contains v if {
    v := input.role2
}
`
		schema := []byte(`{"type":"object","properties":{"role1":{"type":"string"},"role2":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		// Two occurrence functions + a combinator define-fun for roles
		if !strings.Contains(result.SmtContent, "define-fun roles") {
			t.Errorf("expected define-fun for roles in SMT output:\n%s", result.SmtContent)
		}
		if !strings.Contains(result.SmtContent, "roles_1") || !strings.Contains(result.SmtContent, "roles_2") {
			t.Errorf("expected occurrence functions roles_1 and roles_2:\n%s", result.SmtContent)
		}
	})

	// A contains rule used via subscript in another rule's body.
	// allow if { allowed_roles[input.role] } holds when allowed_roles(input.role) returns (OBoolean true).
	t.Run("ContainsUsedInBody", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

allowed_roles contains v if {
    v := input.role
}

allow if {
    allowed_roles[input.role]
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// Multiple contains rules; the body uses a subscript to check membership.
	t.Run("IncrementalContainsUsedInBody", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

roles contains v if {
    v := input.role1
}

roles contains v if {
    v := input.role2
}

allow if {
    roles[input.role1]
}
`
		schema := []byte(`{"type":"object","properties":{"role1":{"type":"string"},"role2":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// Contains rule with a numeric key derived from input.
	t.Run("ContainsNumericKey", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

valid_ids contains v if {
    v := input.id
}

allow if {
    valid_ids[input.id]
}
`
		schema := []byte(`{"type":"object","properties":{"id":{"type":"integer"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// Subscripted contains rule: reasons[item.id] contains message if { ... }
	// translates as a two-parameter predicate reasons(subscript_key, contains_val).
	t.Run("SubscriptedContainsRule_SmtOutput", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

reasons[item.id] contains message if {
    item := input.item
    message := item.label
}
`
		schema := []byte(`{
			"type": "object",
			"properties": {
				"item": {
					"type": "object",
					"properties": {
						"id":    {"type": "integer"},
						"label": {"type": "string"}
					},
					"additionalProperties": false
				}
			},
			"additionalProperties": false
		}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		// The generated SMT must define a two-parameter function for reasons.
		if !strings.Contains(result.SmtContent, "define-fun reasons") {
			t.Errorf("expected define-fun for reasons in SMT output:\n%s", result.SmtContent)
		}
	})

	// Dotted-path contains rule: rule.a.b contains value if { ... }
	// Constant string path elements are encoded in the function name (rule_a_b),
	// only the contains key variable is a parameter.
	t.Run("DottedPathContains_SmtOutput", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

rule.a.b contains value if {
    value := input.role
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		// The SMT must define a function named rule (path encoded as Seq String parameter).
		if !strings.Contains(result.SmtContent, "define-fun rule") {
			t.Errorf("expected define-fun rule in SMT output:\n%s", result.SmtContent)
		}
		// The function signature must include the Seq String path parameter.
		if !strings.Contains(result.SmtContent, "(Seq String)") {
			t.Errorf("expected (Seq String) path parameter in SMT output:\n%s", result.SmtContent)
		}
	})

	// Dotted-path contains used in a body: allow if { rule.a.b[input.role] }
	t.Run("DottedPathContains_UsedInBody", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

rule.a.b contains value if {
    value := input.role
}

allow if {
    rule.a.b[input.role]
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
	})

	// Dotted-path rule: rule.a.b := v if { body }.  The generated assertion constrains
	// the nested field rule["a"]["b"] rather than the base object itself.
	t.Run("DottedPathRule_SmtOutput", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

rule.a.b := v if {
    v := 1
}
`
		schema := []byte(`{"type":"object","additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		// The SMT must assert something about the field, not the whole object.
		if !strings.Contains(result.SmtContent, `"a"`) || !strings.Contains(result.SmtContent, `"b"`) {
			t.Errorf("expected field path \"a\"/\"b\" in SMT output:\n%s", result.SmtContent)
		}
	})

	// Dotted-path rule with body constraint; Z3 must find a satisfying model.
	t.Run("DottedPathRule_BodyConstraint", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

rule.status := v if {
    v := input.active
}
`
		schema := []byte(`{"type":"object","properties":{"active":{"type":"boolean"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if !strings.Contains(result.SmtContent, `"status"`) {
			t.Errorf("expected field path \"status\" in SMT output:\n%s", result.SmtContent)
		}
	})

	// Two dotted-path rules defining different fields of the same base object are
	// translated as independent field assertions, not combined as incremental rules.
	t.Run("DottedPathRule_MultipleFields", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

rule.x := v1 if { v1 := 1 }
rule.y := v2 if { v2 := 2 }
`
		schema := []byte(`{"type":"object","additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if !strings.Contains(result.SmtContent, `"x"`) || !strings.Contains(result.SmtContent, `"y"`) {
			t.Errorf("expected both field paths \"x\" and \"y\" in SMT output:\n%s", result.SmtContent)
		}
	})

	// Contains rule where the satisfying model must fix input.role.
	// Since allow requires allowed_roles[input.role], and allowed_roles(v) is true iff
	// v == input.role (both from the same field), Z3 must assign input.role some string.
	t.Run("ContainsInputKeyUsedInBody_ModelCheck", func(t *testing.T) {
		t.Parallel()
		rego := `
package test

allowed_roles contains v if {
    v := input.role
}

allow if {
    allowed_roles[input.role]
}
`
		schema := []byte(`{"type":"object","properties":{"role":{"type":"string"}},"additionalProperties":false}`)
		result, err := RunPolicyToModel(rego, schema, nil)
		if err != nil {
			t.Fatalf("RunPolicyToModel error: %v", err)
		}
		if _, ok := result.Vars["allow"]; !ok {
			t.Errorf("expected 'allow' in model vars, got: %v", varKeys(result.Vars))
		}
		// The satisfying model must include input
		inputVal, ok := result.Vars["input"]
		if !ok {
			t.Fatalf("expected 'input' in model vars")
		}
		inputMap, ok := inputVal.Map()
		if !ok {
			t.Fatalf("expected input to be a map, got kind: %s", inputVal.Kind())
		}
		roleVal, ok := inputMap["role"]
		if !ok {
			t.Fatalf("expected 'role' field in input map")
		}
		if roleVal.Kind() != modelPkg.ValueString {
			t.Errorf("expected input.role to be a string, got kind: %s", roleVal.Kind())
		}
	})
}
