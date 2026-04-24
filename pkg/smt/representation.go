package smt

import (
	"fmt"
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

// Representation of values assignable to Rego variables
type SmtValue struct {
	value   string
	depth   int
	atomics []types.AtomicType
	isConst bool // true if value is int / string / boolean ...
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
	// handle constant types
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
		case types.AtomicNull: // maybe not necessary
			wrapper = "ONull"
		case types.AtomicUndef: // maybe not necessary
			wrapper = "OUndef"
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
	for d := sv.depth - 1; d > depth; d-- {
		value = fmt.Sprintf("(wrap%d %s)", d, value)
	}
	return &SmtValue{value: value, depth: depth, atomics: sv.atomics}
}

func (sv *SmtValue) SelectObj(at string) *SmtValue {
	value := fmt.Sprintf("(select (obj%d %s) \"%s\")", sv.depth, sv.value, at)
	return NewSmtValue(value, sv.depth-1)
}

func (sv *SmtValue) SelectArr(at int) *SmtValue {
	value := fmt.Sprintf("(select (arr%d %s) %d)", sv.depth, sv.value, at)
	return NewSmtValue(value, sv.depth-1)
}

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

func (sv *SmtValue) findAtomicValue() string {
	s := sv.value
	if s[0] != '(' {
		return sv.value
	}

	idx := strings.Index(s, ")")
	if idx == -1 {
		return ""
	}

	// Take substring before first ')'
	sub := s[:idx]

	// Trim trailing spaces
	sub = strings.TrimSpace(sub)

	if sub == "" {
		return ""
	}

	// Walk backwards to find last word
	end := len(sub)
	start := end

	for start > 0 && sub[start-1] != ' ' {
		start--
	}

	return sub[start:end]
}

func (sv *SmtValue) getBool() *SmtProposition {
	v, err := sv.AsBool()
	if err != nil {
		return RawProposition("false")
	}
	return RawProposition(v.value) // v is unwrapped
}

func (sv *SmtValue) TypeIs(t types.AtomicType) bool {
	for _, at := range sv.atomics {
		if at == t {
			return true
		}
	}
	return false
}

// Holds makes a test whether given value satisfies rule body
//
// Returns:
//
// string: The test SMT representation
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

func (sv *SmtValue) AsString() (*SmtValue, error) {
	if !sv.TypeIs(types.AtomicString) {
		return nil, verr.ErrUnexpectedValueType(sv.String(), "string")
	}

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

func (sv *SmtValue) AsInt() (*SmtValue, error) {
	if !sv.TypeIs(types.AtomicInt) {
		return nil, verr.ErrUnexpectedValueType(sv.String(), "int")
	}

	if sv.depth == -1 {
		return sv, nil
	}

	if sv.isConst {
		v := sv.findAtomicValue()
		i, err := strconv.Atoi(v)
		if err != nil {
			return nil, err
		}
		return NewSmtValueFromInt(i), nil
	}

	value := fmt.Sprintf("(num %s)", sv.UnwrapToDepth(0))
	return &SmtValue{value: value, depth: -1, atomics: []types.AtomicType{types.AtomicInt}, isConst: true}, nil
}

func (sv *SmtValue) AsBool() (*SmtValue, error) {
	if !sv.TypeIs(types.AtomicBoolean) {
		return nil, verr.ErrUnexpectedValueType(sv.String(), "bool")
	}

	if sv.depth == -1 {
		return sv, nil
	}

	if sv.isConst {
		v := sv.findAtomicValue()
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

func (sv *SmtValue) AsArgType(t ArgType) (*SmtValue, error) {
	switch t.atomic {
	case types.AtomicBoolean:
		return sv.AsBool()
	case types.AtomicString:
		return sv.AsString()
	case types.AtomicInt:
		return sv.AsInt()
	}

	return sv.WrapToDepth(t.depth), nil
}

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

func Let(localVar varDef, value *SmtValue) *SmtValue {
	val := fmt.Sprintf("(let ((%s %s)) %s)", localVar.string, localVar.SmtValue.String(), value.String())
	return NewSmtValue(val, value.depth)
}

func Lets(localVars []varDef, value *SmtValue) *SmtValue {
	if len(localVars) == 0 {
		return value
	}
	val := ""
	for _, v := range localVars {
		val += fmt.Sprintf(" (%s %s)", v.string, v.SmtValue.String())
	}
	return NewSmtValue(fmt.Sprintf("(let (%s) %s)", val[1:], value.String()), value.depth)
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

type Arg struct {
	string
	int
}

func DefineFun(name string, args []Arg, body *SmtValue) *SmtCommand {
	argStr := "("
	if len(args) == 0 {
		argStr += "()"
	}
	for _, a := range args {
		argStr += fmt.Sprintf("(%s %s)", a.string, NewSmtType(uint(a.int)).String())
	}
	argStr += ")"

	typ := NewSmtType(uint(body.depth))

	value := fmt.Sprintf("(define-fun %s %s %s %s)", name, argStr, typ.String(), body.String())
	return &SmtCommand{value: value}
}
