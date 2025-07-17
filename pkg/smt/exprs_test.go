package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

func newDummyTranslator() *Translator {
	// Setup a dummy type analyzer with some schema variables
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"input.parameters.foo": types.NewAtomicType(types.AtomicString),
			"input.parameters.bar": types.NewAtomicType(types.AtomicInt),
			"input.data.x":         types.NewObjectType(map[string]types.RegoTypeDef{"y": types.NewAtomicType(types.AtomicBoolean)}),
		},
		Refs: map[string]ast.Value{},
	}
	return &Translator{
		TypeInfo: ta,
	}
}

func TestRefToSmt_InputSimple(t *testing.T) {
	t.Parallel()
	tr := newDummyTranslator()
	ref := ast.MustParseRef("input.foo")
	_, err := tr.refToSmt(ref)
	if err == nil {
		t.Errorf("expected error for missing type, got nil")
	}
}

func TestRefToSmt_InputParameters(t *testing.T) {
	t.Parallel()
	tr := newDummyTranslator()
	ref := ast.MustParseRef("input.parameters.foo")
	smt, err := tr.refToSmt(ref)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	// Should be a select chain or just the variable, depending on the type
	if smt == "" || !strings.Contains(smt, "input.parameters.foo") {
		t.Errorf("expected SMT string to contain 'input.parameters.foo', got %q", smt)
	}
}

func TestRefToSmt_InputSchemaPath(t *testing.T) {
	t.Parallel()
	tr := newDummyTranslator()
	ref := ast.MustParseRef("input.parameters.foo.bar.baz")
	tr.TypeInfo.Types["input.parameters.foo"] = types.NewObjectType(map[string]types.RegoTypeDef{
		"bar": types.NewObjectType(map[string]types.RegoTypeDef{
			"baz": types.NewAtomicType(types.AtomicString),
		}),
	})
	smt, err := tr.refToSmt(ref)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !(strings.Contains(smt, "select") && strings.Contains(smt, "bar") && strings.Contains(smt, "baz")) {
		t.Errorf("expected select chain with 'bar' and 'baz', got %q", smt)
	}
}

func TestRefToSmt_EmptyRef(t *testing.T) {
	t.Parallel()
	tr := newDummyTranslator()
	ref := ast.Ref{}
	smt, err := tr.refToSmt(ref)
	if err == nil {
		t.Errorf("expected error for empty ref, got nil")
	}
	if smt != "" {
		t.Errorf("expected empty string, got %q", smt)
	}
}

func TestRefToSmt_NonInputRef(t *testing.T) {
	t.Parallel()
	tr := newDummyTranslator()
	ref := ast.MustParseRef("data.x.y")
	smt, err := tr.refToSmt(ref)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if smt != ref.String() {
		t.Errorf("expected %q, got %q", ref.String(), smt)
	}
}

func TestRefToSmt_InputDataReviewNestedObject(t *testing.T) {
	t.Parallel()
	tr := newDummyTranslator()
	// Setup nested type: input.data.review.foo.bar.baz
	tr.TypeInfo.Types["input.data.review.foo"] = types.NewObjectType(map[string]types.RegoTypeDef{
		"bar": types.NewObjectType(map[string]types.RegoTypeDef{
			"baz": types.NewAtomicType(types.AtomicString),
		}),
	})

	// Test direct field
	ref1 := ast.MustParseRef("input.data.review.foo")
	smt1, err1 := tr.refToSmt(ref1)
	if err1 != nil {
		t.Fatalf("unexpected error: %v", err1)
	}
	if !strings.Contains(smt1, "input.data.review.foo") {
		t.Errorf("expected select chain with 'foo', got %q", smt1)
	}

	// Test deeper nested field
	ref2 := ast.MustParseRef("input.data.review.foo.bar")
	smt2, err2 := tr.refToSmt(ref2)
	if err2 != nil {
		t.Fatalf("unexpected error: %v", err2)
	}
	if !(strings.Contains(smt2, "select") && strings.Contains(smt2, "foo") && strings.Contains(smt2, "bar")) {
		t.Errorf("expected select chain with 'foo' and 'bar', got %q", smt2)
	}

	// Test full path
	ref3 := ast.MustParseRef("input.data.review.foo.bar.baz")
	smt3, err3 := tr.refToSmt(ref3)
	if err3 != nil {
		t.Fatalf("unexpected error: %v", err3)
	}
	if !(strings.Contains(smt3, "select") && strings.Contains(smt3, "foo") && strings.Contains(smt3, "bar") && strings.Contains(smt3, "baz")) {
		t.Errorf("expected select chain with 'foo', 'bar', 'baz', got %q", smt3)
	}

	// Test missing type for nested path
	ref4 := ast.MustParseRef("input.data.review.unknownfield")
	_, err4 := tr.refToSmt(ref4)
	if err4 == nil {
		t.Errorf("expected error for missing type in nested path, got nil")
	}
}

func TestTermToSmt_BasicTypes(t *testing.T) {
	tr := newDummyTranslator()
	tests := []struct {
		name    string
		term    *ast.Term
		want    string
		wantErr bool
	}{
		{"string", ast.NewTerm(ast.String("foo")), `"foo"`, false},
		{"number", ast.NewTerm(ast.Number("42")), "42", false},
		{"boolean true", ast.NewTerm(ast.Boolean(true)), "true", false},
		{"boolean false", ast.NewTerm(ast.Boolean(false)), "false", false},
		{"var", ast.NewTerm(ast.Var("x")), "x", false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := tr.termToSmt(tt.term)
			if (err != nil) != tt.wantErr {
				t.Errorf("termToSmt() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if got != tt.want {
				t.Errorf("termToSmt() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestExprToSmt_BasicOps(t *testing.T) {
	tr := newDummyTranslator()
	// expr: plus(1, 2) => (+ 1 2)
	plusExpr := ast.Expr{
		Terms: []*ast.Term{
			ast.NewTerm(ast.String("plus")),
			ast.NewTerm(ast.Number("1")),
			ast.NewTerm(ast.Number("2")),
		},
	}
	got, err := tr.exprToSmt(plusExpr)
	if err != nil {
		t.Errorf("exprToSmt() error = %v", err)
	}
	want := "(+ 1 2)"
	if got != want {
		t.Errorf("exprToSmt() = %v, want %v", got, want)
	}

	// expr: eq("foo", "foo") => (= "foo" "foo")
	eqExpr := ast.Expr{
		Terms: []*ast.Term{
			ast.NewTerm(ast.String("eq")),
			ast.NewTerm(ast.String("foo")),
			ast.NewTerm(ast.String("foo")),
		},
	}
	got, err = tr.exprToSmt(eqExpr)
	if err != nil {
		t.Errorf("exprToSmt() error = %v", err)
	}
	want = "(= \"foo\" \"foo\")"
	if got != want {
		t.Errorf("exprToSmt() = %v, want %v", got, want)
	}
}

func TestExprToSmt_Advanced(t *testing.T) {
	tr := newDummyTranslator()

	cases := []struct {
		name    string
		expr    ast.Expr
		want    string
		wantErr bool
	}{
		{
			name: "neq operator",
			expr: ast.Expr{
				Terms: []*ast.Term{
					ast.NewTerm(ast.String("neq")),
					ast.NewTerm(ast.Number("1")),
					ast.NewTerm(ast.Number("2")),
				},
			},
			want:    "(not (= 1 2))",
			wantErr: false,
		},
		{
			name: "gt operator",
			expr: ast.Expr{
				Terms: []*ast.Term{
					ast.NewTerm(ast.String("gt")),
					ast.NewTerm(ast.Number("3")),
					ast.NewTerm(ast.Number("2")),
				},
			},
			want:    "(> 3 2)",
			wantErr: false,
		},
		{
			name: "lt operator",
			expr: ast.Expr{
				Terms: []*ast.Term{
					ast.NewTerm(ast.String("lt")),
					ast.NewTerm(ast.Number("1")),
					ast.NewTerm(ast.Number("2")),
				},
			},
			want:    "(< 1 2)",
			wantErr: false,
		},
		{
			name: "equal operator",
			expr: ast.Expr{
				Terms: []*ast.Term{
					ast.NewTerm(ast.String("equal")),
					ast.NewTerm(ast.Number("5")),
					ast.NewTerm(ast.Number("5")),
				},
			},
			want:    "(= 5 5)",
			wantErr: false,
		},
		{
			name: "unsupported operator",
			expr: ast.Expr{
				Terms: []*ast.Term{
					ast.NewTerm(ast.String("foo")),
					ast.NewTerm(ast.Number("1")),
				},
			},
			want:    "",
			wantErr: true,
		},
	}

	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			got, err := tr.exprToSmt(tt.expr)
			if (err != nil) != tt.wantErr {
				t.Errorf("exprToSmt() error = %v, wantErr %v", err, tt.wantErr)
			}
			if got != tt.want {
				t.Errorf("exprToSmt() = %q, want %q", got, tt.want)
			}
		})
	}
}
