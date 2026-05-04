package smt

import (
	"fmt"
	"slices"
	"strconv"
	"strings"

	"github.com/open-policy-agent/opa/v1/ast"
	verr "github.com/vhavlena/verirego/pkg/err"
	"github.com/vhavlena/verirego/pkg/types"
)

// RawProposition creates a proposition from a raw SMT-LIB boolean term.
func RawProposition(value string) *SmtProposition {
	return &SmtProposition{value: value}
}

// Representation of types of Rego variables
type SmtType struct {
	depth uint
}

func (st *SmtType) String() string {
	return fmt.Sprintf("OTypeD%v", st.depth)
}

func NewSmtType(depth uint) *SmtType {
	return &SmtType{depth: depth}
}

// Representation of SMT values
type SmtValue struct {
	value   string             // corresponding SMT code, such as "(ONumber 1)"
	depth   int                // depth of the value (same as in RegoTypeDef). depth = -1 is used for literals, e.g., "1", or "true".
	atomics []types.AtomicType // list of all atomic types
	isConst bool               // true if value is a Rego literal (used for optimization)
}

func NewSmtValue(value string, depth int) *SmtValue {
	return &SmtValue{value: value, depth: depth}
}

func NewSmtValueFromString(str string) *SmtValue {
	value := fmt.Sprintf("\"%s\"", str)
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicString}, isConst: true}
}

func NewSmtValueFromInt(i int) *SmtValue {
	value := fmt.Sprintf("%d", i)
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicInt}, isConst: true}
}

func NewSmtValueFromBoolean(b bool) *SmtValue {
	value := fmt.Sprintf("%v", b)
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicBoolean}, isConst: true}
}

// getAtomicTypes returns a list of all possible atomic types present in the input RegoTypeDef
func getAtomicTypes(tp types.RegoTypeDef) []types.AtomicType {
	types := make([]types.AtomicType, 0)
	if tp.IsAtomic() {
		types = append(types, tp.AtomicType)
	}
	if tp.IsUnion() {
		for _, t := range tp.Union {
			types = append(types, getAtomicTypes(t)...)
		}
	}
	return types
}

// NewSmtValueFromVar creates SmtValue for given variable.
// Its depth and atomic types are extracted from the input exprTrans.
func NewSmtValueFromVar(v ast.Var, exprTrans *ExprTranslator) (*SmtValue, error) {
	name := removeQuotes(v.String())
	tp, ok := exprTrans.TypeTrans.TypeInfo.Types[name]
	if !ok {
		return nil, verr.ErrTypeNotFound(name)
	}
	types := getAtomicTypes(tp)
	return &SmtValue{
		value:   name,
		depth:   tp.TypeDepth(),
		atomics: types,
	}, nil
}

func (sv *SmtValue) GetDepth() int {
	return sv.depth
}

func (sv *SmtValue) String() string {
	return sv.value
}

// WrapToDepth creates a smt value wrapped to a given depth
// If the given depth is more than the current value depth, nothing happens
// It is the user's responsibility to manage this
//
// Parameters:
//
// depth int: depth of the final SMT value
//
// Returns:
//
// &SmtValue: the wrapped value
//
// Example:
//
// WrapToDepth(valD0, 3) is (Wrap3 (Wrap2 (Wrap1 valD0)))
func (sv *SmtValue) WrapToDepth(depth int) *SmtValue {
	value := sv.value
	// handle constant values, such as "1" or "(num foo)"
	if sv.depth == -1 {
		if len(sv.atomics) != 1 {
			return nil // TODO: maybe return err, but it would make it inconvenient
		}
		wrapper := ""
		switch sv.atomics[0] {
		case types.AtomicBoolean:
			wrapper = "OBoolean"
		case types.AtomicInt:
			wrapper = "ONumber"
		case types.AtomicString:
			wrapper = "OString"
		default:
			return nil
		}
		// sv will now have depth of 0, which is easily wrappable
		value = fmt.Sprintf("(%s %s)", wrapper, sv.value)
		sv.depth += 1
	}
	for d := sv.depth + 1; d <= depth; d++ {
		value = fmt.Sprintf("(Wrap%d %s)", d, value)
	}
	return &SmtValue{value: value, depth: depth, atomics: sv.atomics}
}

// UnwrapToDepth creates a smt value unwrapped to a given depth
// If the given depth is more than the current value depth, nothing happens
// It is the user's responsibility to manage this
//
// Parameters:
//
// depth int: depth of the final SMT value
//
// Returns:
//
// SmtValue: the unwrapped value
//
// Example:
//
// UnwrapToDepth(valD3, 0) is (wrap1 (wrap2 (wrap3 valD3)))
func (sv *SmtValue) UnwrapToDepth(depth int) *SmtValue {
	value := sv.value
	for d := sv.depth; d > depth; d-- {
		value = fmt.Sprintf("(wrap%d %s)", d, value)
	}
	return &SmtValue{value: value, depth: depth, atomics: sv.atomics}
}

// SelectObj performs a selection of SmtValue sv (representing an object) at specified key.
func (sv *SmtValue) SelectObj(at string) *SmtValue {
	value := fmt.Sprintf("(select (obj%d %s) %s)", sv.depth, sv.value, at)
	return NewSmtValue(value, sv.depth-1)
}

// SelectArr performs a selection of SmtValue sv (representing an array) at specified key.
func (sv *SmtValue) SelectArr(at string) *SmtValue {

// 	(ite 
//   ;; IF: Index 0 je v rámci hranic pole
//   (< 0 (seq.len (arr1 (select (obj2 (select (obj3 input) "user")) "numero"))))
  
//   ;; THEN: Vrať skutečný prvek z pole
//   (seq.nth (arr1 (select (obj2 (select (obj3 input) "user")) "numero")) 0)
  
//   ;; ELSE: Vrať tvůj vlastní OUndef (Simulace JS undefined)
//   OUndef
// )
	preambule := fmt.Sprintf("(ite (< 0 (seq.len (arr%d %s)))", sv.depth, sv.value)
	undef := fmt.Sprintf("OUndef")
	value := fmt.Sprintf("(seq.nth (arr%d %s) %s)", sv.depth, sv.value, at)
	concat := fmt.Sprintf("%s %s %s)", preambule, value, undef)
	return NewSmtValue(concat, sv.depth-1)
}

// Equals returns a proposition corresponding to equality of the two given SmtValues.
// It automatically aligns the two values to the same depth.
func (sv *SmtValue) Equals(other *SmtValue) *SmtProposition {
	d := max(sv.depth, other.depth)
	value := fmt.Sprintf("(= %s %s)", sv.WrapToDepth(d).String(), other.WrapToDepth(d).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsString() *SmtProposition {
	if sv.isConst && sv.TypeIs(types.AtomicString) {
		return RawProposition("true")
	}
	value := fmt.Sprintf("(is-OString %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsNumber() *SmtProposition {
	if sv.isConst && sv.TypeIs(types.AtomicInt) {
		return RawProposition("true")
	}
	value := fmt.Sprintf("(is-ONumber %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsBoolean() *SmtProposition {
	if sv.isConst && sv.TypeIs(types.AtomicBoolean) {
		return RawProposition("true")
	}
	value := fmt.Sprintf("(is-OBoolean %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsNull() *SmtProposition {
	if sv.isConst && sv.TypeIs(types.AtomicNull) {
		return RawProposition("true")
	}
	value := fmt.Sprintf("(is-ONull %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsUndef() *SmtProposition {
	if sv.isConst && sv.TypeIs(types.AtomicUndef) {
		return RawProposition("true")
	}
	value := fmt.Sprintf("(is-OUndef %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

// findConstValue gets a constant value from SMT representation.
// sv is expected to be (potentially Wrapped) constant literal, such as "1", or "(Wrap2 (ONumber 1))"
// This function should not be used for Strings (for this case, use findConstString).
func (sv *SmtValue) findConstValue() string {
	s := sv.value
	if s[0] != '(' {
		return sv.value
	}

	// Take substring before first ')'
	before, _, ok := strings.Cut(s, ")")
	if !ok {
		return ""
	}
	before = strings.TrimSpace(before)

	if before == "" {
		return ""
	}

	// Walk backwards to find last word
	end := len(before)
	start := end

	for start > 0 && before[start-1] != ' ' {
		start--
	}

	return before[start:end]
}

// getBool accesses the boolean value of given SmtValue and returns it.
// If the SmtValue could not be interpreted as a boolean, "false" is returned.
func (sv *SmtValue) getBool() *SmtProposition {
	v, err := sv.AsBool()
	if err != nil {
		return RawProposition("false")
	}
	return RawProposition(v.value) // v is unwrapped
}

func (sv *SmtValue) TypeIs(t types.AtomicType) bool {
	return slices.Contains(sv.atomics, t)
}

// Holds makes a test whether given value satisfies rule body
//
// Returns:
//
//	string: The test SMT representation
func (sv *SmtValue) Holds() *SmtProposition {
	propositions := make([]SmtProposition, 0)
	if sv.TypeIs(types.AtomicUndef) {
		propositions = append(propositions, *sv.IsUndef().Not())
	}
	if sv.TypeIs(types.AtomicBoolean) {
		propositions = append(propositions, *sv.getBool())
	}
	return And(propositions)
}

// findConstString gets a string from SmtValue, such as (OString "abc")
func findConstString(sv *SmtValue) (string, error) {
	s := sv.value
	start := strings.Index(s, "\"")
	if start == -1 {
		return "", fmt.Errorf("smt value %s does not contain a string literal", sv.String())
	}
	s = s[start:]
	end := strings.Index(s[1:], "\"")
	if end == -1 {
		return "", fmt.Errorf("smt value %s does not contain a string literal", sv.String())
	}
	return s[:end+2], nil
}

// AsString returns the input SmtValue interpreted as a string, e.g., (str x).
func (sv *SmtValue) AsString() (*SmtValue, error) {
	if !sv.TypeIs(types.AtomicString) {
		return nil, verr.ErrUnexpectedValueType(sv.String(), "string")
	}

	// In this case, value is already extracted
	if sv.depth == -1 {
		return sv, nil
	}

	if sv.isConst {
		v, err := findConstString(sv)
		if err != nil {
			return nil, err
		}
		return NewSmtValueFromString(v), nil
	}

	value := fmt.Sprintf("(str %s)", sv.UnwrapToDepth(0))
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicString}, isConst: true}, nil
}

// AsInt returns the input SmtValue interpreted as an integer, e.g., (num x).
func (sv *SmtValue) AsInt() (*SmtValue, error) {
	if !sv.TypeIs(types.AtomicInt) {
		return nil, verr.ErrUnexpectedValueType(sv.String(), "int")
	}

	// In this case, value is already extracted
	if sv.depth == -1 {
		return sv, nil
	}

	if sv.isConst {
		v := sv.findConstValue()
		i, err := strconv.Atoi(v)
		if err != nil {
			return nil, err
		}
		return NewSmtValueFromInt(i), nil
	}

	value := fmt.Sprintf("(num %s)", sv.UnwrapToDepth(0))
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicInt}, isConst: true}, nil
}

// AsBool returns the input SmtValue interpreted as a boolean, e.g., (bool x).
func (sv *SmtValue) AsBool() (*SmtValue, error) {
	if !sv.TypeIs(types.AtomicBoolean) {
		return nil, verr.ErrUnexpectedValueType(sv.String(), "bool")
	}

	// In this case, value is already extracted
	if sv.depth == -1 {
		return sv, nil
	}

	if sv.isConst {
		v := sv.findConstValue()
		if v == "true" {
			return NewSmtValueFromBoolean(true), nil
		}
		if v == "false" {
			return NewSmtValueFromBoolean(false), nil
		}
	}

	value := fmt.Sprintf("(bool %s)", sv.UnwrapToDepth(0))
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicBoolean}, isConst: true}, nil
}

// AsArgType returns the input SmtValue intepreted as the given ArgType.
func (sv *SmtValue) AsArgType(t ArgType) (*SmtValue, error) {
	if t.depth == -1 {
		switch t.atomic {
		case types.AtomicBoolean:
			return sv.AsBool()
		case types.AtomicString:
			return sv.AsString()
		case types.AtomicInt:
			return sv.AsInt()
		}
	}

	return sv.WrapToDepth(t.depth), nil
}

// Ite creates a SMT "if-then-else" construct.
func Ite(condition *SmtProposition, thenClause *SmtValue, elseClause *SmtValue) *SmtValue {
	if condition.isTrue() {
		return thenClause
	}
	if condition.isFalse() {
		return elseClause
	}
	depth := max(thenClause.depth, elseClause.depth, 0)
	ite := fmt.Sprintf("(ite %s %s %s)", condition.String(), thenClause.WrapToDepth(depth).String(), elseClause.WrapToDepth(depth).String())
	return NewSmtValue(ite, depth)
}

// Ite creates a SMT "let" statement, introducing a local variable to the given clause.
func Let(localVar varDef, value *SmtValue) *SmtValue {
	lName := localVar.name
	lVal  := localVar.value
	val := fmt.Sprintf("(let ((%s %s)) %s)", lName, lVal.String(), value.String())
	return &SmtValue{value: val, depth: value.depth, atomics: value.atomics}
}

func ExistQuantif(name string, depth int, value *SmtValue) *SmtValue {
	val := fmt.Sprintf("(exists ((%s %s)) %s)", name, NewSmtType(uint(depth)), value.value)
	return NewSmtValue(val, value.depth)
}

// SmtProposition represents a boolean value
type SmtProposition struct {
	value string
}

func (sp *SmtProposition) isTrue() bool {
	return sp.value == "true"
}

func (sp *SmtProposition) isFalse() bool {
	return sp.value == "false"
}

func (sp SmtProposition) String() string {
	return sp.value
}

func (sp SmtProposition) Not() *SmtProposition {
	value := fmt.Sprintf("(not %s)", sp.value)
	return &SmtProposition{value: value}
}

// IntoValue transforms interprets given proposition as a SmtValue
func (sp *SmtProposition) IntoValue() *SmtValue {
	return &SmtValue{
		value:   sp.value,
		depth:   -1,
		atomics: []types.AtomicType{types.AtomicBoolean},
	}
}

type propositionStringer interface {
	String() string
}

// combineProps builds an SMT-LIB boolean term (e.g. (and ...) / (or ...)) from a slice of items.
//
// Semantics are intentionally kept consistent with the existing helpers in this package:
// - empty => true
// - single => the single proposition string; if it's already an *SmtProposition, return it as-is
func combineProps[T propositionStringer](op string, props []T) *SmtProposition {
	switch len(props) {
	case 0:
		return &SmtProposition{value: "true"}
	case 1:
		if p, ok := any(props[0]).(*SmtProposition); ok {
			return p
		}
		return &SmtProposition{value: props[0].String()}
	default:
		var sb strings.Builder
		sb.WriteByte('(')
		sb.WriteString(op)
		for _, p := range props {
			sb.WriteByte(' ')
			sb.WriteString(p.String())
		}
		sb.WriteByte(')')
		return &SmtProposition{value: sb.String()}
	}
}

// AndPtrs builds an SMT-LIB (and ...) from proposition pointers.
// - empty => true
// - single => that proposition
func AndPtrs(props []*SmtProposition) *SmtProposition {
	return combineProps("and", props)
}

// OrPtrs builds an SMT-LIB (or ...) from proposition pointers.
// - empty => true
// - single => that proposition
func OrPtrs(props []*SmtProposition) *SmtProposition {
	return combineProps("or", props)
}

func And(props []SmtProposition) *SmtProposition {
	return combineProps("and", props)
}

func Or(props []SmtProposition) *SmtProposition {
	return combineProps("or", props)
}

// SmtCommand represents a top-level SMT command, such as assert, define-func, etc.
type SmtCommand struct {
	value string
}

func (sc *SmtCommand) String() string {
	return sc.value
}

// RawCommand wraps a raw SMT-LIB top-level command.
func RawCommand(value string) *SmtCommand {
	return &SmtCommand{value: value}
}

// Assert creates a top-level SMT assertion of given proposition.
func Assert(sp *SmtProposition) *SmtCommand {
	value := fmt.Sprintf("(assert %s)", sp.String())
	return &SmtCommand{value: value}
}

// DeclareVar declares a 0-arity symbol of a given sort.
func DeclareVar(name string, sort string) *SmtCommand {
	value := fmt.Sprintf("(declare-fun %s () %s)", name, sort)
	return &SmtCommand{value: value}
}

// DeclareFun declares a function symbol with parameter sorts and return sort.
func DeclareFun(name string, paramSorts []string, retSort string) *SmtCommand {
	value := fmt.Sprintf("(declare-fun %s (%s) %s)", name, strings.Join(paramSorts, " "), retSort)
	return &SmtCommand{value: value}
}

// DefineFun creates a SMT function definition.
// The return type is derived from the function body.
func DefineFun(name string, args []Arg, body *SmtValue) *SmtCommand {
	argStr := "("
	if len(args) == 0 {
		argStr += "()"
	}
	for _, a := range args {
		argStr += fmt.Sprintf("(%s %s)", a.name, NewSmtType(uint(a.typ.depth)).String())
	}
	argStr += ")"

	typ := NewSmtType(uint(body.depth))

	value := fmt.Sprintf("(define-fun %s %s %s %s)", name, argStr, typ.String(), body.String())
	return &SmtCommand{value: value}
}
