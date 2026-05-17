package smt

import (
	"strings"
	"testing"
)

// TestMetadata_NamePrefix_AppliedToDefineFun verifies that setting a NamePrefix on
// TranslatorMetadata causes every define-fun in the SMT output to carry the prefix,
// while the semantics (Z3 model result) remain identical to the un-prefixed run.
//
// The policy uses two incremental parametric rules so the translation emits three
// define-fun forms: two per-occurrence helpers and one top-level combinator.  With
// prefix "pfx_", the expected names are pfx_foo_1, pfx_foo_2, and pfx_foo.
func TestMetadata_NamePrefix_AppliedToDefineFun(t *testing.T) {
	const prefix = "pfx_"
	rego := `
package test
foo(x) := 1 if { x > 10 }
foo(x) := 2 if { x > 0 }
p := foo(5)
`
	result, err := RunPolicyToModelWithMeta(rego, nil, nil, TranslatorMetadata{
		EntryPoint: "p",
		NamePrefix: prefix,
	})
	if err != nil {
		t.Fatalf("RunPolicyToModelWithMeta error: %v", err)
	}

	// Semantic check: second rule fires for foo(5) since 5 <= 10 but 5 > 0.
	pVal, ok := result.Vars["p"]
	if !ok {
		t.Fatalf("expected 'p' in model vars, got: %v", varKeys(result.Vars))
	}
	num, ok := pVal.Int64()
	if !ok || num != 2 {
		t.Fatalf("expected p == 2 (second occurrence fires), got: %v", num)
	}

	// Structural check: all module-level define-fun names must carry the prefix.
	// Compare_N_K functions are global type infrastructure (like declare-datatypes)
	// and are intentionally not prefixed.
	for _, line := range strings.Split(result.SmtContent, "\n") {
		if !strings.HasPrefix(line, "(define-fun ") {
			continue
		}
		// Extract the function name (token after "(define-fun ").
		rest := strings.TrimPrefix(line, "(define-fun ")
		name := strings.SplitN(rest, " ", 2)[0]
		if strings.HasPrefix(name, "Compare_") {
			continue
		}
		if !strings.HasPrefix(name, prefix) {
			t.Errorf("define-fun %q is missing prefix %q", name, prefix)
		}
	}

	// Sanity check: the prefixed occurrence names must actually appear.
	for _, want := range []string{"pfx_foo_1", "pfx_foo_2", "pfx_foo"} {
		if !strings.Contains(result.SmtContent, want) {
			t.Errorf("expected %q in SMT output, not found", want)
		}
	}
}
