package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/types"
)

func newDummyExprTranslator() *ExprTranslator {
	// Setup a dummy type analyzer with some schema variables
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"input.parameters.foo": types.NewAtomicType(types.AtomicString),
			"input.parameters.bar": types.NewAtomicType(types.AtomicInt),
			"input.data.x":         types.NewObjectType(map[string]types.RegoTypeDef{"y": types.NewAtomicType(types.AtomicBoolean)}),
		},
		Refs: map[string]ast.Value{},
	}
	typeTrans := NewTypeDefs(ta)
	return NewExprTranslator(typeTrans)
}

func newTestExprTranslatorWithTypes(typeMap map[string]types.RegoTypeDef) *ExprTranslator {
	ta := &types.TypeAnalyzer{
		Types: typeMap,
		Refs:  map[string]ast.Value{},
	}
	typeTrans := NewTypeDefs(ta)
	return NewExprTranslator(typeTrans)
}

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
	return NewTranslator(ta, nil)
}

func TestRefToSmt_InputSimple(t *testing.T) {
	t.Parallel()
	et := newDummyExprTranslator()
	ref := ast.MustParseRef("input.foo")
	_, err := et.refToSmt(ref)
	if err == nil {
		t.Errorf("expected error for missing type, got nil")
	}
}

func TestRefToSmt_InputParameters(t *testing.T) {
	t.Parallel()
	et := newDummyExprTranslator()
	ref := ast.MustParseRef("input.parameters.foo")
	smt, err := et.refToSmt(ref)
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
	et := newDummyExprTranslator()
	ref := ast.MustParseRef("input.parameters.foo.bar.baz")
	et.TypeTrans.TypeInfo.Types["input.parameters.foo"] = types.NewObjectType(map[string]types.RegoTypeDef{
		"bar": types.NewObjectType(map[string]types.RegoTypeDef{
			"baz": types.NewAtomicType(types.AtomicString),
		}),
	})
	smt, err := et.refToSmt(ref)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !(strings.Contains(smt, "select") && strings.Contains(smt, "bar") && strings.Contains(smt, "baz")) {
		t.Errorf("expected select chain with 'bar' and 'baz', got %q", smt)
	}
}

func TestRefToSmt_EmptyRef(t *testing.T) {
	t.Parallel()
	et := newDummyExprTranslator()
	ref := ast.Ref{}
	smt, err := et.refToSmt(ref)
	if err == nil {
		t.Errorf("expected error for empty ref, got nil")
	}
	if smt != "" {
		t.Errorf("expected empty string, got %q", smt)
	}
}

func TestRefToSmt_NonInputRef(t *testing.T) {
	t.Parallel()
	et := newDummyExprTranslator()
	ref := ast.MustParseRef("data.x.y")
	// Ensure the type translator knows the type for this non-input reference
	et.TypeTrans.TypeInfo.Types[ref.String()] = types.NewAtomicType(types.AtomicInt)

	smt, err := et.refToSmt(ref)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	// For an atomic int the SMT representation should be (num (atom <name>))
	expected := "(num (atom " + ref.String() + "))"
	if smt != expected {
		t.Errorf("expected %q, got %q", expected, smt)
	}
}

func TestRefToSmt_InputDataReviewNestedObject(t *testing.T) {
	t.Parallel()
	et := newDummyExprTranslator()
	// Setup nested type: input.data.review.foo.bar.baz
	et.TypeTrans.TypeInfo.Types["input.data.review.foo"] = types.NewObjectType(map[string]types.RegoTypeDef{
		"bar": types.NewObjectType(map[string]types.RegoTypeDef{
			"baz": types.NewAtomicType(types.AtomicString),
		}),
	})

	// Test direct field
	ref1 := ast.MustParseRef("input.data.review.foo")
	smt1, err1 := et.refToSmt(ref1)
	if err1 != nil {
		t.Fatalf("unexpected error: %v", err1)
	}
	if !strings.Contains(smt1, "input.data.review.foo") {
		t.Errorf("expected select chain with 'foo', got %q", smt1)
	}

	// Test deeper nested field
	ref2 := ast.MustParseRef("input.data.review.foo.bar")
	smt2, err2 := et.refToSmt(ref2)
	if err2 != nil {
		t.Fatalf("unexpected error: %v", err2)
	}
	if !(strings.Contains(smt2, "select") && strings.Contains(smt2, "foo") && strings.Contains(smt2, "bar")) {
		t.Errorf("expected select chain with 'foo' and 'bar', got %q", smt2)
	}

	// Test full path
	ref3 := ast.MustParseRef("input.data.review.foo.bar.baz")
	smt3, err3 := et.refToSmt(ref3)
	if err3 != nil {
		t.Fatalf("unexpected error: %v", err3)
	}
	if !(strings.Contains(smt3, "select") && strings.Contains(smt3, "foo") && strings.Contains(smt3, "bar") && strings.Contains(smt3, "baz")) {
		t.Errorf("expected select chain with 'foo', 'bar', 'baz', got %q", smt3)
	}

	// Test missing type for nested path
	ref4 := ast.MustParseRef("input.data.review.unknownfield")
	_, err4 := et.refToSmt(ref4)
	if err4 == nil {
		t.Errorf("expected error for missing type in nested path, got nil")
	}
}

func TestTermToSmt_BasicTypes(t *testing.T) {
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
		{"var", ast.NewTerm(ast.Var("x")), "(num (atom x))", false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			et := newDummyExprTranslator()

			// If the term is a variable, ensure the type analyzer knows its type
			if _, isVar := tt.term.Value.(ast.Var); isVar {
				et.TypeTrans.TypeInfo.Types[tt.term.Value.String()] = types.NewAtomicType(types.AtomicInt)
			}
			got, err := et.termToSmt(tt.term)
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
	et := newDummyExprTranslator()
	// expr: plus(1, 2) => (+ 1 2)
	plusExpr := ast.Expr{
		Terms: []*ast.Term{
			ast.NewTerm(ast.String("plus")),
			ast.NewTerm(ast.Number("1")),
			ast.NewTerm(ast.Number("2")),
		},
	}
	got, err := et.ExprToSmt(&plusExpr)
	if err != nil {
		t.Errorf("exprToSmt() error = %v", err)
	}
	want := "(+ 1 2)"
	if got != want {
		t.Errorf("exprToSmt() = %v, want %v", got, want)
	}

	// expr: eq("foo", "foo") => (= "foo" "foo")
	eqExpr := &ast.Expr{
		Terms: []*ast.Term{
			ast.NewTerm(ast.String("eq")),
			ast.NewTerm(ast.String("foo")),
			ast.NewTerm(ast.String("foo")),
		},
	}
	got, err = et.ExprToSmt(eqExpr)
	if err != nil {
		t.Errorf("exprToSmt() error = %v", err)
	}
	want = "(= \"foo\" \"foo\")"
	if got != want {
		t.Errorf("exprToSmt() = %v, want %v", got, want)
	}
}

func TestExprToSmt_Advanced(t *testing.T) {

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
			et := newDummyExprTranslator()
			got, err := et.ExprToSmt(&tt.expr)
			if (err != nil) != tt.wantErr {
				t.Errorf("exprToSmt() error = %v, wantErr %v", err, tt.wantErr)
			}
			if got != tt.want {
				t.Errorf("exprToSmt() = %q, want %q", got, tt.want)
			}
		})
	}
}

func TestExplicitArrayToSmt_Success(t *testing.T) {
	et := newDummyExprTranslator()
	// Add type info for the array string representation
	arr := ast.NewArray(ast.IntNumberTerm(1), ast.IntNumberTerm(2), ast.IntNumberTerm(3))
	arrStr := arr.String()
	et.TypeTrans.TypeInfo.Types[arrStr] = types.NewArrayType(types.NewAtomicType(types.AtomicInt))
	got, err := et.explicitArrayToSmt(arr)
	if err != nil {
		t.Fatalf("expected no error, got: %v", err)
	}

	// Create a translator to test the context merging
	tr := newDummyTranslator()
	tr.AddTransContext(et.GetTransContext())

	if got == "" {
		t.Errorf("expected non-empty SMT var name, got empty string")
	}
	// More sophisticated checks: variable name format and side effects
	if !strings.HasPrefix(got, "const_arr") {
		t.Errorf("expected SMT var name to start with 'const_arr_', got %q", got)
	}
	// Check that a declaration and assertion were added
	if len(tr.smtDecls) == 0 {
		t.Errorf("expected at least one SMT declaration, got none")
	}
	if len(tr.smtAsserts) == 0 {
		t.Errorf("expected at least one SMT assertion, got none")
	}
}

func TestExplicitArrayToSmt_TypeNotFound(t *testing.T) {
	et := newDummyExprTranslator()
	arr := ast.NewArray(ast.IntNumberTerm(1), ast.IntNumberTerm(2))
	_, err := et.explicitArrayToSmt(arr)
	if err == nil {
		t.Fatalf("expected error for missing type info, got nil")
	}
}

func TestExprToSmt_AllCases(t *testing.T) {
	t.Parallel()
	t.Run("Builtins", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"plus": types.NewAtomicType(types.AtomicInt),
			"1":    types.NewAtomicType(types.AtomicInt),
			"2":    types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		expr := ast.MustParseExpr("plus(1,2)")
		smt, err := et.ExprToSmt(expr)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		expected := "(+ 1 2)"
		if smt != expected {
			t.Errorf("expected %q, got %q", expected, smt)
		}
	})

	t.Run("Neq", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"neq": types.NewAtomicType(types.AtomicBoolean),
			"1":   types.NewAtomicType(types.AtomicInt),
			"2":   types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		expr := ast.MustParseExpr("neq(1,2)")
		smt, err := et.ExprToSmt(expr)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		expected := "(not (= 1 2))"
		if smt != expected {
			t.Errorf("expected %q, got %q", expected, smt)
		}
	})

	t.Run("Uninterpreted", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"foo": types.NewAtomicType(types.AtomicString),
			"1":   types.NewAtomicType(types.AtomicInt),
			"2":   types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		expr := ast.MustParseExpr("foo(1,2)")
		smt, err := et.ExprToSmt(expr)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		// The function name will be a fresh variable, so just check the format
		if len(et.context.Bucket.Decls) == 0 {
			t.Errorf("expected a function declaration in smtDecls")
		}
		decl := et.context.Bucket.Decls[len(et.context.Bucket.Decls)-1]
		if decl == "" || decl[:13] != "(declare-fun " {
			t.Errorf("expected function declaration, got %q", decl)
		}
		if smt[:1] != "(" || smt[len(smt)-1:] != ")" {
			t.Errorf("expected function application format, got %q", smt)
		}
	})

	t.Run("TypeError", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"foo": types.NewAtomicType(types.AtomicFunction),
			// missing type for "1"
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		expr := ast.MustParseExpr("foo(1)")
		_, err := et.ExprToSmt(expr)
		if err == nil {
			t.Errorf("expected error for missing type, got nil")
		}
	})
}

func TestExplicitArrayToSmt_CompareFullSmtLib(t *testing.T) {
	arrTerm := ast.MustParseTerm(`[1, 2, 3]`)
	arr, ok := arrTerm.Value.(*ast.Array)
	if !ok {
		t.Fatalf("expected ast.Array, got %T", arrTerm.Value)
	}

	typeMap := map[string]types.RegoTypeDef{
		arr.String(): types.NewArrayType(types.NewAtomicType(types.AtomicInt)),
	}
	et := newTestExprTranslatorWithTypes(typeMap)
	varName, err := et.explicitArrayToSmt(arr)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	// Create a translator to test the context merging
	tr := newDummyTranslator()
	tr.AddTransContext(et.GetTransContext())

	if varName == "" {
		t.Fatalf("expected non-empty SMT var name")
	}

	var sb strings.Builder
	for _, decl := range tr.smtDecls {
		sb.WriteString(decl)
		sb.WriteString("\n")
	}
	for _, asrt := range tr.smtAsserts {
		sb.WriteString(asrt)
		sb.WriteString("\n")
	}
	smtlib := sb.String()

	expectedDeclPrefix := "(declare-fun " + varName + " () OTypeD0)"
	expectedElem0 := "(assert (= (select (arr " + varName + ") 0) 1))"
	expectedElem1 := "(assert (= (select (arr " + varName + ") 1) 2))"
	expectedElem2 := "(assert (= (select (arr " + varName + ") 2) 3))"

	if !strings.Contains(smtlib, expectedDeclPrefix) {
		t.Errorf("expected SMT-LIB to contain declaration: %q\nGot:\n%s", expectedDeclPrefix, smtlib)
	}
	if !strings.Contains(smtlib, expectedElem0) {
		t.Errorf("expected SMT-LIB to contain: %q\nGot:\n%s", expectedElem0, smtlib)
	}
	if !strings.Contains(smtlib, expectedElem1) {
		t.Errorf("expected SMT-LIB to contain: %q\nGot:\n%s", expectedElem1, smtlib)
	}
	if !strings.Contains(smtlib, expectedElem2) {
		t.Errorf("expected SMT-LIB to contain: %q\nGot:\n%s", expectedElem2, smtlib)
	}
}

func TestHandleConstObject_AllCases(t *testing.T) {
	t.Parallel()

	t.Run("SimpleObject", func(t *testing.T) {
		objTerm := ast.MustParseTerm(`{"name": "test", "value": 42}`)
		obj, ok := objTerm.Value.(ast.Object)
		if !ok {
			t.Fatalf("expected ast.Object, got %T", objTerm.Value)
		}
		typeMap := map[string]types.RegoTypeDef{
			obj.String(): types.NewObjectType(map[string]types.RegoTypeDef{
				"name":  types.NewAtomicType(types.AtomicString),
				"value": types.NewAtomicType(types.AtomicInt),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		varName, err := et.handleConstObject(obj)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}

		// Create a translator to test the context merging
		tr := newDummyTranslator()
		tr.AddTransContext(et.GetTransContext())

		if varName == "" {
			t.Fatalf("expected non-empty variable name")
		}
		joined := strings.Join(append(tr.smtDecls, tr.smtAsserts...), "\n")
		expected := "(declare-fun " + varName + " () OTypeD0)\n(assert (and (is-OString (atom (select (obj " + varName + ") \"name\"))) (is-ONumber (atom (select (obj " + varName + ") \"value\")))))"
		if joined != expected {
			t.Errorf("SMT output mismatch.\nGot:   %q\nWant: %q", joined, expected)
		}
	})

	t.Run("TypeNotFound", func(t *testing.T) {
		objTerm := ast.MustParseTerm(`{"key": "value"}`)
		obj, ok := objTerm.Value.(ast.Object)
		if !ok {
			t.Fatalf("expected ast.Object, got %T", objTerm.Value)
		}
		et := newDummyExprTranslator()
		_, err := et.handleConstObject(obj)
		if err == nil {
			t.Fatalf("expected error for missing type info, got nil")
		}
	})

	t.Run("NestedObject", func(t *testing.T) {
		objTerm := ast.MustParseTerm(`{"user": {"name": "john", "age": 30}, "active": true}`)
		obj, ok := objTerm.Value.(ast.Object)
		if !ok {
			t.Fatalf("expected ast.Object, got %T", objTerm.Value)
		}
		typeMap := map[string]types.RegoTypeDef{
			obj.String(): types.NewObjectType(map[string]types.RegoTypeDef{
				"user": types.NewObjectType(map[string]types.RegoTypeDef{
					"name": types.NewAtomicType(types.AtomicString),
					"age":  types.NewAtomicType(types.AtomicInt),
				}),
				"active": types.NewAtomicType(types.AtomicBoolean),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		varName, err := et.handleConstObject(obj)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}

		// Create a translator to test the context merging
		tr := newDummyTranslator()
		tr.AddTransContext(et.GetTransContext())

		if varName == "" {
			t.Fatalf("expected non-empty variable name")
		}
		joined := strings.Join(append(tr.smtDecls, tr.smtAsserts...), "\n")
		expected := "(declare-fun const_obj () OTypeD1)\n(assert (and (is-OBoolean (atom (select (obj const_obj) \"active\"))) (is-OObj (select (obj const_obj) \"user\")) (is-ONumber (atom (select (obj (select (obj const_obj) \"user\")) \"age\"))) (is-OString (atom (select (obj (select (obj const_obj) \"user\")) \"name\")))))"
		if joined != expected {
			t.Errorf("SMT output mismatch.\nGot:   %q\nWant: %q", joined, expected)
		}
	})

	t.Run("EmptyObject", func(t *testing.T) {
		objTerm := ast.MustParseTerm(`{}`)
		obj, ok := objTerm.Value.(ast.Object)
		if !ok {
			t.Fatalf("expected ast.Object, got %T", objTerm.Value)
		}
		typeMap := map[string]types.RegoTypeDef{
			obj.String(): types.NewObjectType(map[string]types.RegoTypeDef{}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		varName, err := et.handleConstObject(obj)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}

		// Create a translator to test the context merging
		tr := newDummyTranslator()
		tr.AddTransContext(et.GetTransContext())

		if varName == "" {
			t.Fatalf("expected non-empty variable name")
		}
		if len(tr.smtDecls) == 0 {
			t.Errorf("expected at least one SMT declaration, got none")
		}
		if len(tr.smtAsserts) == 0 {
			t.Errorf("expected at least one SMT assertion, got none")
		}
	})

	t.Run("CompareFullSmtLib", func(t *testing.T) {
		objTerm := ast.MustParseTerm(`{"status": "active", "count": 5}`)
		obj, ok := objTerm.Value.(ast.Object)
		if !ok {
			t.Fatalf("expected ast.Object, got %T", objTerm.Value)
		}
		typeMap := map[string]types.RegoTypeDef{
			obj.String(): types.NewObjectType(map[string]types.RegoTypeDef{
				"status": types.NewAtomicType(types.AtomicString),
				"count":  types.NewAtomicType(types.AtomicInt),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		varName, err := et.handleConstObject(obj)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}

		// Create a translator to test the context merging
		tr := newDummyTranslator()
		tr.AddTransContext(et.GetTransContext())

		if varName == "" {
			t.Fatalf("expected non-empty variable name")
		}
		var sb strings.Builder
		for _, decl := range tr.smtDecls {
			sb.WriteString(decl)
			sb.WriteString("\n")
		}
		for _, asrt := range tr.smtAsserts {
			sb.WriteString(asrt)
			sb.WriteString("\n")
		}
		smtlib := sb.String()
		expectedDeclPrefix := "(declare-fun " + varName + " () OTypeD"
		if !strings.Contains(smtlib, expectedDeclPrefix) {
			t.Errorf("expected SMT-LIB to contain declaration prefix: %q\nGot:\n%s", expectedDeclPrefix, smtlib)
		}
		expectedConstraintPrefix := "(assert (and"
		if !strings.Contains(smtlib, expectedConstraintPrefix) {
			t.Errorf("expected SMT-LIB to contain constraint assertion: %q\nGot:\n%s", expectedConstraintPrefix, smtlib)
		}
		if !strings.Contains(smtlib, varName) {
			t.Errorf("expected SMT-LIB to contain variable name %q in assertions\nGot:\n%s", varName, smtlib)
		}
	})

	t.Run("ObjectWithArray", func(t *testing.T) {
		objTerm := ast.MustParseTerm(`{"items": [1, 2, 3], "name": "list"}`)
		obj, ok := objTerm.Value.(ast.Object)
		if !ok {
			t.Fatalf("expected ast.Object, got %T", objTerm.Value)
		}
		typeMap := map[string]types.RegoTypeDef{
			obj.String(): types.NewObjectType(map[string]types.RegoTypeDef{
				"items": types.NewArrayType(types.NewAtomicType(types.AtomicInt)),
				"name":  types.NewAtomicType(types.AtomicString),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		varName, err := et.handleConstObject(obj)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}

		// Create a translator to test the context merging
		tr := newDummyTranslator()
		tr.AddTransContext(et.GetTransContext())

		if varName == "" {
			t.Fatalf("expected non-empty variable name")
		}
		if len(tr.smtDecls) == 0 {
			t.Errorf("expected at least one SMT declaration, got none")
		}
		if len(tr.smtAsserts) == 0 {
			t.Errorf("expected at least one SMT assertion, got none")
		}
	})
}
