package smt

import (
	"testing"
)

// TestObjCmp exercises the Compare_N_K equality-modulo-wrap functions through
// the full pipeline: parse → compile → inline → type-infer → SMT-translate → Z3.
//
// Design notes for these tests:
//
//   - Scalar (atomic) fields must only appear in depth-1 objects, i.e. the very
//     last layer of nesting.  A scalar field inside a depth-≥2 object causes the
//     existing type-constraint generator to emit predicates at the wrong sort (a
//     pre-existing issue unrelated to Compare_N_K).
//
//   - Rule names must not clash with SMT-LIB accessor symbols (obj1, obj2, atom1,
//     wrap1, …) used in the emitted datatype declarations.
//
//   - When the comparison body is expected to be false (objects differ), the rule
//     assigns `OUndef` to `allow`, which violates its boolean type constraint and
//     makes the formula UNSAT.  Adding `default allow := false` prevents this by
//     supplying a boolean fallback so the formula stays SAT regardless.

// TestObjCmp_FlatEqual verifies that comparing two structurally identical
// depth-1 objects is SAT and causes allow to fire.
func TestObjCmp_FlatEqual(t *testing.T) {
	t.Parallel()
	rego := `
package test
p := {"a": 1, "b": 2}
q := {"a": 1, "b": 2}
allow if {
    p == q
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	if _, ok := result.Vars["allow"]; !ok {
		t.Errorf("expected 'allow' to fire (p == q), vars: %v", varKeys(result.Vars))
	}
}

// TestObjCmp_FlatUnequal verifies that comparing a depth-1 object rule result
// with a literal of the same type but a different value does not cause allow to
// fire.  Using an inline literal on one side avoids the leaf-variable collision
// that arises when two rule-defined objects share the same field name.
// The `default allow := false` keeps the formula SAT when the comparison fails.
func TestObjCmp_FlatUnequal(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
p := {"a": 1}
allow if {
    p == {"a": 2}
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	av, ok := result.Vars["allow"]
	if !ok {
		t.Fatalf("expected 'allow' in model (from default), vars: %v", varKeys(result.Vars))
	}
	b, isBool := av.Bool()
	if !isBool || b {
		t.Errorf("expected allow == false (p != {\"a\":2}), got: %v", av)
	}
}

// TestObjCmp_NestedEqual verifies that comparing two depth-2 objects (one level
// of object nesting, scalar at the innermost layer) is SAT and causes allow to fire.
func TestObjCmp_NestedEqual(t *testing.T) {
	t.Parallel()
	rego := `
package test
lhs := {"x": {"y": 10}}
rhs := {"x": {"y": 10}}
allow if {
    lhs == rhs
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	if _, ok := result.Vars["allow"]; !ok {
		t.Errorf("expected 'allow' to fire (lhs == rhs), vars: %v", varKeys(result.Vars))
	}
}

// TestObjCmp_NestedUnequal verifies that a depth-2 rule result compared with a
// structurally identical but value-different inline literal does not fire allow.
func TestObjCmp_NestedUnequal(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
lhs := {"x": {"y": 10}}
allow if {
    lhs == {"x": {"y": 20}}
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	av, ok := result.Vars["allow"]
	if !ok {
		t.Fatalf("expected 'allow' in model (from default), vars: %v", varKeys(result.Vars))
	}
	b, isBool := av.Bool()
	if !isBool || b {
		t.Errorf("expected allow == false (lhs != {x:{y:20}}), got: %v", av)
	}
}

// TestObjCmp_NestedFieldAccess is the primary motivating example.
//
// p := {"d": {"e": {"f": 7}}} ; all-object chain, scalar only at depth 1
// q := {"e": {"f": 7}}
// allow if { p.d == q }       ; p.d and q are both depth-2 objects → Compare_2_2
func TestObjCmp_NestedFieldAccess(t *testing.T) {
	t.Parallel()
	rego := `
package test
p := {"d": {"e": {"f": 7}}}
q := {"e": {"f": 7}}
allow if {
    p.d == q
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	av, ok := result.Vars["allow"]
	if !ok {
		t.Errorf("expected 'allow' to fire (p.d == q), vars: %v", varKeys(result.Vars))
	}
	b, isBool := av.Bool()
	if !isBool || !b {
		t.Errorf("expected allow == true (p.d == q), got: %v", av)
	}
}

// TestObjCmp_NestedFieldAccessUnequal verifies that a field access compared
// with an inline literal of different value does not cause allow to fire.
func TestObjCmp_NestedFieldAccessUnequal(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
p := {"d": {"e": {"f": 7}}}
allow if {
    p.d == {"e": {"f": 99}}
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	av, ok := result.Vars["allow"]
	if !ok {
		t.Fatalf("expected 'allow' in model (from default), vars: %v", varKeys(result.Vars))
	}
	b, isBool := av.Bool()
	if !isBool || b {
		t.Errorf("expected allow == false (p.d != {e:{f:99}}), got: %v", av)
	}
}

// TestObjCmp_ThreeLevelChain compares a three-level all-object chain accessed via
// field lookup.  p.outer and q are both depth-2 objects → Compare_2_2.
func TestObjCmp_ThreeLevelChain(t *testing.T) {
	t.Parallel()
	rego := `
package test
p := {"outer": {"inner": {"leaf": 42}}}
q := {"inner": {"leaf": 42}}
allow if {
    p.outer == q
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	if _, ok := result.Vars["allow"]; !ok {
		t.Errorf("expected 'allow' to fire (p.outer == q), vars: %v", varKeys(result.Vars))
	}
}

// TestObjCmp_TwoRulesEqual checks that two rule results with the same nested
// structure are equal.  Variable names avoid clashing with SMT accessor names.
func TestObjCmp_TwoRulesEqual(t *testing.T) {
	t.Parallel()
	rego := `
package test
myobj_a := {"x": {"y": 10}}
myobj_b := {"x": {"y": 10}}
allow if {
    myobj_a == myobj_b
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	if _, ok := result.Vars["allow"]; !ok {
		t.Errorf("expected 'allow' to fire (myobj_a == myobj_b), vars: %v", varKeys(result.Vars))
	}
}

// TestObjCmp_TwoRulesUnequal verifies that a rule result compared with an
// inline literal of different value is not considered equal.
func TestObjCmp_TwoRulesUnequal(t *testing.T) {
	t.Parallel()
	rego := `
package test
default allow := false
myobj := {"x": {"y": 10}}
allow if {
    myobj == {"x": {"y": 20}}
}
`
	result, err := RunPolicyToModel(rego, nil, nil)
	if err != nil {
		t.Fatalf("RunPolicyToModel error: %v", err)
	}
	av, ok := result.Vars["allow"]
	if !ok {
		t.Fatalf("expected 'allow' in model (from default), vars: %v", varKeys(result.Vars))
	}
	b, isBool := av.Bool()
	if !isBool || b {
		t.Errorf("expected allow == false (myobj != {x:{y:20}}), got: %v", av)
	}
}
