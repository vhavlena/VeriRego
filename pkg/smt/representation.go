package smt

import (
	"fmt"
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
}

func NewSmtValue(value string, depth int) *SmtValue {
	return &SmtValue{value: value, depth: depth}
}

func NewSmtValueFromString(str string) *SmtValue {
	value := fmt.Sprintf("(OString \"%s\")", str)
	return &SmtValue{value: value, depth: 0, atomics: []types.AtomicType{types.AtomicString}}
}

func NewSmtValueFromInt(i int) *SmtValue {
	value := fmt.Sprintf("(ONumber %d)", i)
	return &SmtValue{value: value, depth: 0, atomics: []types.AtomicType{types.AtomicInt}}
}

func NewSmtValueFromBoolean(b bool) *SmtValue {
	value := fmt.Sprintf("(OBoolean %v)", b)
	return &SmtValue{value: value, depth: 0, atomics: []types.AtomicType{types.AtomicBoolean}}
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
		return nil, verr.ErrTypeNotFound
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
	for d := sv.depth + 1; d <= depth; d++ {
		value = fmt.Sprintf("(Wrap%d %s)", d, value)
	}
	return NewSmtValue(value, depth)
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
	return NewSmtValue(value, depth)
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
	value := fmt.Sprintf("(is-OString %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsNumber() *SmtProposition {
	value := fmt.Sprintf("(is-ONumber %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsBoolean() *SmtProposition {
	value := fmt.Sprintf("(is-OBoolean %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsNull() *SmtProposition {
	value := fmt.Sprintf("(is-ONull %s)", sv.UnwrapToDepth(0).String())
	return &SmtProposition{value: value}
}

func (sv *SmtValue) IsUndef() *SmtProposition {
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
	if !sv.TypeIs(types.AtomicBoolean) {
		return sv.IsBoolean() // this should not happen
	}
	// unwrap "true" / "false" for efficiency
	v := sv.findAtomicValue()
	if v == "true" {
		return RawProposition("true")
	}
	if v == "false" {
		return RawProposition("false")
	}

	value := fmt.Sprintf("(bool %s)", sv.UnwrapToDepth(0))
	return RawProposition(value)
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

func Ite(condition *SmtProposition, thenClause *SmtValue, elseClause *SmtValue) *SmtValue {
	if condition.isTrue() {
		return thenClause
	}
	if condition.isFalse() {
		return elseClause
	}
	depth := max(thenClause.depth, elseClause.depth)
	ite := fmt.Sprintf("(ite %s %s %s)", condition.String(), thenClause.WrapToDepth(depth).String(), elseClause.WrapToDepth(depth).String())
	return NewSmtValue(ite, depth)
}

func Let(localVars []varDef, value *SmtValue) *SmtValue {
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

func DefineFunc(name string, args map[string]SmtValue, typeDepth uint, body SmtValue) *SmtCommand {
	argStr := "("
	if len(args) == 0 {
		argStr += "()"
	}
	for k, v := range args {
		argStr += fmt.Sprintf("(%s %s)", k, v.String())
	}
	argStr += ")"

	typ := NewSmtType(typeDepth)

	value := fmt.Sprintf("(define-func %s %s %s %s)", name, argStr, typ.String(), body.String())
	return &SmtCommand{value: value}
}
