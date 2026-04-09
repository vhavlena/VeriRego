package smt

import (
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
	"github.com/vhavlena/verirego/pkg/simplify"
	"github.com/vhavlena/verirego/pkg/types"
)

func newDummyExprTranslator() *ExprTranslator {
	// Setup a dummy type analyzer with some schema variables.
	// The root key is "input" (the new architecture); nested fields are
	// accessed via the path resolution in refToSmtValue.
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"data": types.NewObjectType(map[string]types.RegoTypeDef{
					"x": types.NewObjectType(map[string]types.RegoTypeDef{
						"y": types.NewAtomicType(types.AtomicBoolean),
					}),
				}),
			}),
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
	// Setup a dummy type analyzer with some schema variables.
	// The root key is "input" (the new architecture).
	ta := &types.TypeAnalyzer{
		Types: map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"data": types.NewObjectType(map[string]types.RegoTypeDef{
					"x": types.NewObjectType(map[string]types.RegoTypeDef{
						"y": types.NewAtomicType(types.AtomicBoolean),
					}),
				}),
			}),
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
	// For an atomic int the SMT representation should be (num <name>)
	expected := "(num " + ref.String() + ")"
	if smt != expected {
		t.Errorf("expected %q, got %q", expected, smt)
	}
}

func TestRefToSmt_InputDataReviewNestedObject(t *testing.T) {
	t.Parallel()
	et := newDummyExprTranslator()
	// Schema root is "input"; fields are accessed via select chains.
	et.TypeTrans.TypeInfo.Types["input"] = types.NewObjectType(map[string]types.RegoTypeDef{
		"foo": types.NewObjectType(map[string]types.RegoTypeDef{
			"bar": types.NewObjectType(map[string]types.RegoTypeDef{
				"baz": types.NewAtomicType(types.AtomicString),
			}),
		}),
	})

	// input.foo → (select (obj<d> input) "foo")
	ref1 := ast.MustParseRef("input.foo")
	smt1, err1 := et.refToSmt(ref1)
	if err1 != nil {
		t.Fatalf("unexpected error: %v", err1)
	}
	if !(strings.Contains(smt1, "select") && strings.Contains(smt1, "input") && strings.Contains(smt1, "foo")) {
		t.Errorf("expected select expression referencing 'input' and 'foo', got %q", smt1)
	}

	// input.foo.bar → nested select chain
	ref2 := ast.MustParseRef("input.foo.bar")
	smt2, err2 := et.refToSmt(ref2)
	if err2 != nil {
		t.Fatalf("unexpected error: %v", err2)
	}
	if !(strings.Contains(smt2, "select") && strings.Contains(smt2, "foo") && strings.Contains(smt2, "bar")) {
		t.Errorf("expected select chain with 'foo' and 'bar', got %q", smt2)
	}

	// input.foo.bar.baz → full path
	ref3 := ast.MustParseRef("input.foo.bar.baz")
	smt3, err3 := et.refToSmt(ref3)
	if err3 != nil {
		t.Fatalf("unexpected error: %v", err3)
	}
	if !(strings.Contains(smt3, "select") && strings.Contains(smt3, "foo") && strings.Contains(smt3, "bar") && strings.Contains(smt3, "baz")) {
		t.Errorf("expected select chain with 'foo', 'bar', 'baz', got %q", smt3)
	}

	// input.unknown → field missing from the object type → error
	ref4 := ast.MustParseRef("input.unknown")
	_, err4 := et.refToSmt(ref4)
	if err4 == nil {
		t.Errorf("expected error for missing field 'unknown' in input type, got nil")
	}
}

func TestRefToSmt_DataSchemaField(t *testing.T) {
	t.Parallel()
	// Build an ExprTranslator whose TypeAnalyzer has a DataSchema set.
	dataSchema := types.NewInputSchema()
	if err := dataSchema.ProcessYAMLInput([]byte("token: \"secret\"\ncount: 42\n")); err != nil {
		t.Fatalf("failed to process data YAML: %v", err)
	}
	ta := &types.TypeAnalyzer{
		Types:      map[string]types.RegoTypeDef{},
		Refs:       map[string]ast.Value{},
		DataSchema: dataSchema,
	}
	// Schema root is "data"; fields are accessed via select chains.
	ta.Types["data"] = types.NewObjectType(map[string]types.RegoTypeDef{
		"token": types.NewAtomicType(types.AtomicString),
		"count": types.NewAtomicType(types.AtomicInt),
	})
	typeTrans := NewTypeDefs(ta)
	et := NewExprTranslator(typeTrans)

	// data.token → (str (select (obj1 data) "token"))
	ref1 := ast.MustParseRef("data.token")
	smt1, err1 := et.refToSmt(ref1)
	if err1 != nil {
		t.Fatalf("unexpected error for data.token: %v", err1)
	}
	if !(strings.Contains(smt1, "select") && strings.Contains(smt1, "data") && strings.Contains(smt1, "token")) {
		t.Errorf("expected select expression referencing 'data' and 'token', got %q", smt1)
	}

	// data.count → (num (select (obj1 data) "count"))
	ref2 := ast.MustParseRef("data.count")
	smt2, err2 := et.refToSmt(ref2)
	if err2 != nil {
		t.Fatalf("unexpected error for data.count: %v", err2)
	}
	if !(strings.Contains(smt2, "select") && strings.Contains(smt2, "data") && strings.Contains(smt2, "count")) {
		t.Errorf("expected select expression referencing 'data' and 'count', got %q", smt2)
	}

	// data.unknown → field missing from the object type → error
	ref3 := ast.MustParseRef("data.unknown")
	_, err3 := et.refToSmt(ref3)
	if err3 == nil {
		t.Errorf("expected error for unknown data field, got nil")
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
		{"var", ast.NewTerm(ast.Var("x")), "(num x)", false},
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
		declStr := decl.String()
		if declStr == "" || declStr[:13] != "(declare-fun " {
			t.Errorf("expected function declaration, got %q", declStr)
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
		sb.WriteString(decl.String())
		sb.WriteString("\n")
	}
	for _, asrt := range tr.smtAsserts {
		sb.WriteString(asrt.String())
		sb.WriteString("\n")
	}
	smtlib := sb.String()

	expectedDeclPrefix := "(declare-fun " + varName + " () OTypeD1)"
	expectedElem0 := "(assert (= (select (arr1 " + varName + ") 0) 1))"
	expectedElem1 := "(assert (= (select (arr1 " + varName + ") 1) 2))"
	expectedElem2 := "(assert (= (select (arr1 " + varName + ") 2) 3))"

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
		joined := strings.Join(tr.SmtLines(), "\n")
		expected := "(declare-fun " + varName + " () OTypeD1)\n(assert (and (is-OObj1 " + varName + ") (is-OString (select (obj1 " + varName + ") \"name\")) (is-ONumber (select (obj1 " + varName + ") \"value\"))))"
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
		joined := strings.Join(tr.SmtLines(), "\n")
		expected := "(declare-fun const_obj () OTypeD2)\n(assert (and (is-OObj2 const_obj) (is-OBoolean (select (obj2 const_obj) \"active\")) (is-OObj1 (select (obj2 const_obj) \"user\")) (is-OObj1 (select (obj2 const_obj) \"user\")) (is-ONumber (select (obj1 (select (obj2 const_obj) \"user\")) \"age\")) (is-OString (select (obj1 (select (obj2 const_obj) \"user\")) \"name\"))))"
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
			sb.WriteString(decl.String())
			sb.WriteString("\n")
		}
		for _, asrt := range tr.smtAsserts {
			sb.WriteString(asrt.String())
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

// TestTermToSmtValue_Ref exercises the ast.Ref branch of termToSmtValue.
// After the refactoring, input.* and data.* refs resolve through the object
// root ("input" / "data") rather than per-field type entries, producing
// proper SMT select expressions that are valid Z3.
func TestTermToSmtValue_Ref(t *testing.T) {
	t.Parallel()

	t.Run("InputRefAtomic", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"role": types.NewAtomicType(types.AtomicString),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.role")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		if val == nil {
			t.Fatal("expected non-nil SmtValue")
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "role")) {
			t.Errorf("expected select expression over 'input' accessing 'role', got %q", s)
		}
	})

	t.Run("InputRefInt", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"count": types.NewAtomicType(types.AtomicInt),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.count")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "count")) {
			t.Errorf("expected select expression over 'input' accessing 'count', got %q", s)
		}
	})

	t.Run("InputRefBoolean", func(t *testing.T) {
		t.Parallel()
		typeMap := map[string]types.RegoTypeDef{
			"input": types.NewObjectType(map[string]types.RegoTypeDef{
				"active": types.NewAtomicType(types.AtomicBoolean),
			}),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.active")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "input") && strings.Contains(s, "active")) {
			t.Errorf("expected select expression over 'input' accessing 'active', got %q", s)
		}
	})

	t.Run("InputRefMissingType", func(t *testing.T) {
		t.Parallel()
		// Neither "input" nor "input.x" is in the type map — must error.
		typeMap := map[string]types.RegoTypeDef{
			"x": types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		term := ast.MustParseTerm("input.x")
		_, err := et.termToSmtValue(term)
		if err == nil {
			t.Error("expected error for missing 'input' type, got nil")
		}
	})

	t.Run("DataRefAtomic", func(t *testing.T) {
		t.Parallel()
		dataSchema := types.NewInputJsonSchema()
		typeMap := map[string]types.RegoTypeDef{
			"data": types.NewObjectType(map[string]types.RegoTypeDef{
				"token": types.NewAtomicType(types.AtomicString),
			}),
		}
		ta := &types.TypeAnalyzer{
			Types:      typeMap,
			Refs:       map[string]ast.Value{},
			DataSchema: dataSchema,
		}
		et := NewExprTranslator(NewTypeDefs(ta))
		term := ast.MustParseTerm("data.token")
		val, err := et.termToSmtValue(term)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		s := val.String()
		if !(strings.Contains(s, "select") && strings.Contains(s, "data") && strings.Contains(s, "token")) {
			t.Errorf("expected select expression over 'data' accessing 'token', got %q", s)
		}
	})

	t.Run("NonInputNonDataRef_FallbackToLastComponent", func(t *testing.T) {
		t.Parallel()
		// For refs that are neither input.* nor data.*, we fall back to the last component.
		// Build the ref manually since "some.y" is not valid standalone Rego syntax.
		ref := ast.Ref{
			ast.NewTerm(ast.Var("some")),
			ast.NewTerm(ast.String("y")),
		}
		typeMap := map[string]types.RegoTypeDef{
			"y": types.NewAtomicType(types.AtomicInt),
		}
		et := newTestExprTranslatorWithTypes(typeMap)
		val, err := et.termToSmtValue(ast.NewTerm(ref))
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		if !strings.Contains(val.String(), "y") {
			t.Errorf("expected SMT value to reference 'y', got %q", val.String())
		}
	})
}

// generateSMT is a test helper that runs the compile → inline → type-infer →
// SMT-translate pipeline and returns the raw SMT-LIB string.
func generateSMT(t *testing.T, regoSrc string, jsonSchema []byte) string {
	t.Helper()
	mod, err := ast.ParseModuleWithOpts("p.rego", regoSrc, ast.ParserOptions{RegoVersion: ast.RegoV1})
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	compiler := ast.NewCompiler()
	compiler.Compile(map[string]*ast.Module{mod.Package.Path.String(): mod})
	if compiler.Failed() {
		t.Fatalf("compile error: %v", compiler.Errors)
	}
	compiledModule := compiler.Modules[mod.Package.Path.String()]

	inliner := simplify.NewInliner()
	inliner.GatherInlinePredicates(compiledModule)
	compiledModule = inliner.InlineModule(compiledModule)

	inputSchema := types.InputSchemaAPI(types.NewInputJsonSchema())
	if len(jsonSchema) > 0 {
		js := types.NewInputJsonSchema()
		if err := js.ProcessInput(jsonSchema); err != nil {
			t.Fatalf("json schema error: %v", err)
		}
		inputSchema = js
	}

	typeAnalyzer := types.NewTypeAnalyzerWithParams(mod.Package.Path, inputSchema)
	typeAnalyzer.AnalyzeModule(compiledModule)

	translator := NewTranslator(typeAnalyzer, compiledModule)
	if err := translator.GenerateSmtContent(); err != nil {
		t.Fatalf("smt generation error: %v", err)
	}
	return strings.Join(translator.SmtLines(), "\n")
}

func TestAllowIfSyntax_NotDroppedByInliner(t *testing.T) {
	for _, rego := range []struct{ name, src string }{
		{"allow if", `package example
default allow := false
allow if { 1 == 1 }`},
		{"allow := true if", `package example
default allow := false
allow := true if { 1 == 1 }`},
	} {
		t.Run(rego.name, func(t *testing.T) {
			smt := generateSMT(t, rego.src, nil)
			if !strings.Contains(smt, "(declare-fun allow ()") {
				t.Errorf("expected 'allow' declaration in SMT output (inliner may have dropped the rule):\n%s", smt)
			}
		})
	}
}
