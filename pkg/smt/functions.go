package smt

import (
	"fmt"

	"github.com/open-policy-agent/opa/v1/ast"
	ast_types "github.com/open-policy-agent/opa/v1/types"
	verr "github.com/vhavlena/verirego/pkg/err"
	types "github.com/vhavlena/verirego/pkg/types"
)

// ArgType is a structure holding information about function arguments
// It has depth specified separately, since for builtin functions, it should be -1
// For user-defined functions, it is primarily 0 (may be a subject to change)
type ArgType struct {
	depth  int
	atomic types.AtomicType
}

// Arg represents a named argument, which is used for function definitions.
type Arg struct {
	name string
	typ  ArgType
}

func NewArg(name string, tp types.RegoTypeDef) Arg {
	return Arg{
		name: name,
		typ:  newArgTypeFromTypeDef(tp),
	}
}

// transformType maps Rego ast Type into intermediate AtomicType
func transformType(t ast_types.Type) types.AtomicType {
	switch x := t.(type) {
	case ast_types.Boolean:
		return types.AtomicBoolean
	case ast_types.Number:
		return types.AtomicInt
	case ast_types.Null:
		return types.AtomicNull
	case ast_types.String:
		return types.AtomicString
	case ast_types.Any:
		var atomic types.AtomicType
		for _, t := range x {
			at := transformType(t)
			if at != "" {
				if atomic != "" {
					return ""
				} else {
					atomic = at
				}
			}
		}
		return atomic
	default:
		return ""
	}
}

func NewArgType(t ast_types.Type) ArgType {
	at := transformType(t)
	return ArgType{
		depth:  -1,
		atomic: at,
	}
}

// Function is a structure for handling the conversion of Rego functions into SMT.
type Function struct {
	name        string // for example: eq, plus, ...
	args        []ArgType
	result      ArgType // the return type
	call        callFn  // function for creating the SMT representation of call, w.r.t. the given arguments
	constraints constraintsFn
}

type callFn func(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue, error)

// constraintsFn produces additional SMT top-level commands for a function call.
// It can inspect the produced SMT value as well as the original arguments and
// declared signature to emit extra constraints (assertions, declarations, etc).
// It returns a Bucket containing declarations, asserts and type decls that
// should be merged into the translation context.
type constraintsFn func(callResult *SmtValue, params []*SmtValue, args []ArgType, result ArgType) (*Bucket, error)

// mkSmtFunction creates a callFn function,
// which checks the expected parameter types and creates a SMT value
// of the form "(smtName par1 par2 ...)"
func mkSmtFunction(smtName string) callFn {
	return func(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue, error) {
		if len(args) != len(params) {
			return nil, verr.ErrUnexpected
		}

		callVal := "("
		callVal += smtName
		for i := range args {
			smt, err := params[i].AsArgType(args[i])
			if err != nil {
				return nil, verr.ErrUnexpectedValueType(params[i].String(), string(args[i].atomic))
			}
			callVal += " "
			callVal += smt.String()
		}
		callVal += ")"

		atomics := []types.AtomicType{}
		if result.atomic != "" {
			atomics = append(atomics, result.atomic)
		}
		return &SmtValue{
			value:   callVal,
			depth:   result.depth,
			atomics: atomics,
			isConst: false,
		}, nil
	}
}

// EqFunction checks the equality of its two parameters.
func EqFunction(params []*SmtValue, _ []ArgType, _ ArgType) (*SmtValue, error) {
	if len(params) != 2 {
		return nil, verr.ErrUnexpectedParamCount("=", 2, len(params))
	}

	p1 := params[0]
	p2 := params[1]
	eq := p1.Equals(p2)
	return eq.IntoValue(), nil
}

// NeqFunction checks the inequality of its two parameters.
func NeqFunction(params []*SmtValue, _ []ArgType, _ ArgType) (*SmtValue, error) {
	if len(params) != 2 {
		return nil, verr.ErrUnexpectedParamCount("!=", 2, len(params))
	}

	p1 := params[0]
	p2 := params[1]
	eq := p1.Equals(p2)
	return eq.Not().IntoValue(), nil
}

// generateCaseTemplate creates a nested str.replace_all chain that maps one ASCII
// case range to the other. The template has a single %s placeholder for the input string.
func generateCaseTemplate(fromStart, toStart byte) string {
	template := "%s"
	for offset := int(25); offset >= 0; offset-- {
		src := fromStart + byte(offset)
		dst := toStart + byte(offset)
		template = fmt.Sprintf(`(str.replace_all %s "%c" "%c")`, template, src, dst)
	}
	return template
}

// toLowerTemplate is the pre-computed SMT template for the lower function.
var toLowerTemplate = generateCaseTemplate('A', 'a')

// toUpperTemplate is the pre-computed SMT template for the upper function.
var toUpperTemplate = generateCaseTemplate('a', 'A')

// LowerFunction converts a string to lowercase using nested str.replace_all calls.
func LowerFunction(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue, error) {
	if len(params) != 1 || len(args) != 1 {
		return nil, verr.ErrUnexpectedParamCount("lower", 1, len(params))
	}

	str, err := params[0].AsArgType(args[0])
	if err != nil {
		return nil, verr.ErrUnexpectedValueType(params[0].String(), string(types.AtomicString))
	}

	callVal := fmt.Sprintf(toLowerTemplate, str.String())

	atomics := []types.AtomicType{}
	if result.atomic != "" {
		atomics = append(atomics, result.atomic)
	}

	return &SmtValue{
		value:   callVal,
		depth:   result.depth,
		atomics: []types.AtomicType{types.AtomicString},
		isConst: false,
	}, nil
}

// UpperFunction converts a string to uppercase using nested str.replace_all calls.
func UpperFunction(params []*SmtValue, _ []ArgType, _ ArgType) (*SmtValue, error) {
	if len(params) != 1 {
		return nil, verr.ErrUnexpectedParamCount("upper", 1, len(params))
	}

	str, err := params[0].AsString()
	if err != nil {
		return nil, verr.ErrUnexpectedValueType(params[0].String(), string(types.AtomicString))
	}

	callVal := fmt.Sprintf(toUpperTemplate, str.String())

	return &SmtValue{
		value: callVal,
		// The nested str.replace_all expression has SMT String sort.
		// Keep depth at -1 so callers can wrap to OString when needed.
		depth:   -1,
		atomics: []types.AtomicType{types.AtomicString},
		isConst: false,
	}, nil
}

// TrimFunction represents Rego trim as an uninterpreted SMT function.
// The second argument must be a string literal.
func TrimFunction(params []*SmtValue, args []ArgType, result ArgType) (*SmtValue, error) {
	if len(params) != 2 || len(args) != 2 {
		return nil, verr.ErrUnexpectedParamCount("trim", 2, len(params))
	}

	if !params[1].isConst || !params[1].TypeIs(types.AtomicString) {
		return nil, verr.ErrUnexpectedValueType(params[1].String(), "string literal")
	}

	text, err := params[0].AsArgType(args[0])
	if err != nil {
		return nil, verr.ErrUnexpectedValueType(params[0].String(), string(types.AtomicString))
	}

	chars, err := params[1].AsString()
	if err != nil {
		return nil, verr.ErrUnexpectedValueType(params[1].String(), string(types.AtomicString))
	}

	callVal := fmt.Sprintf("(trim %s %s)", text.String(), chars.String())

	return &SmtValue{
		value:   callVal,
		depth:   result.depth,
		atomics: []types.AtomicType{types.AtomicString},
		isConst: false,
	}, nil
}

// trimConstraints generates SMT constraints about the trim operation.
func trimConstraints(callResult *SmtValue, params []*SmtValue, args []ArgType, result ArgType) (*Bucket, error) {
	// If trimming with an empty string, the result should equal the input: trim(x, "") = x
	bucket := NewBucket()
	if params[1].value == `""` {
		// Extract raw string from input
		inputStr, err := params[0].AsString()
		if err != nil {
			return nil, err
		}
		// Compare raw string values: (assert (= (trim x "") x))
		eqVal := fmt.Sprintf("(= %s %s)", callResult.String(), inputStr.String())
		bucket.Asserts = append(bucket.Asserts, Assert(RawProposition(eqVal)))
		return bucket, nil
	}

	// General case: assert existence of fresh y,z (strings) such that
	// (= x (str.++ y (trim x chars) z))
	y := RandString(8)
	z := RandString(8)
	// declare fresh constants of sort String
	bucket.Decls = append(bucket.Decls, RawCommand(fmt.Sprintf("(declare-const %s String)", y)))
	bucket.Decls = append(bucket.Decls, RawCommand(fmt.Sprintf("(declare-const %s String)", z)))

	// get raw input string expression
	inputStr, err := params[0].AsString()
	if err != nil {
		return nil, err
	}

	// (str.++ y (trim x chars) z) = x
	concat := fmt.Sprintf("(str.++ %s %s %s)", y, callResult.String(), z)
	eqVal := fmt.Sprintf("(= %s %s)", inputStr.String(), concat)
	bucket.Asserts = append(bucket.Asserts, Assert(RawProposition(eqVal)))

	// Build regex constraints:
	// C = charset to trim (from params[1])
	// S/C = all chars except C = re.diff re.allchar C
	// Assert: y and z belong to C*
	// Assert: trim result belongs to (S/C)*

	charsStr := params[1].value // e.g., "\" abc \"" or "\" \""
	// Extract actual string value (remove quotes and unescape)
	charsVal := charsStr
	if len(charsVal) >= 2 && charsVal[0] == '"' && charsVal[len(charsVal)-1] == '"' {
		charsVal = charsVal[1 : len(charsVal)-1]
	}

	// Build regex for C (union of each char)
	cRegex := buildCharsetRegex(charsVal)

	// Build (S/C) = re.diff re.allchar C
	notCRegex := fmt.Sprintf("(re.diff re.allchar %s)", cRegex)

	// Build C* and (S/C)*
	cStar := fmt.Sprintf("(re.* %s)", cRegex)
	notCStar := fmt.Sprintf("(re.* %s)", notCRegex)

	// Assert y in C*
	bucket.Asserts = append(bucket.Asserts,
		Assert(RawProposition(fmt.Sprintf("(str.in_re %s %s)", y, cStar))))

	// Assert z in C*
	bucket.Asserts = append(bucket.Asserts,
		Assert(RawProposition(fmt.Sprintf("(str.in_re %s %s)", z, cStar))))

	// Assert trim result in (S/C)* + ((S/C).S*.(S/C))
	// Build: (re.union (re.* (S/C)) (re.concat (S/C) re.all (S/C)))
	notCConcat := fmt.Sprintf("(re.++ %s re.all %s)", notCRegex, notCRegex)
	trimResultRegex := fmt.Sprintf("(re.union %s %s)", notCStar, notCConcat)
	bucket.Asserts = append(bucket.Asserts,
		Assert(RawProposition(fmt.Sprintf("(str.in_re %s %s)", callResult.String(), trimResultRegex))))

	return bucket, nil
}

// buildCharsetRegex builds an SMT regex that matches any single character in the charset.
// Iterates over Unicode code points (runes) rather than bytes.
// For empty charset, returns re.none. For single char, returns (str.to_re char).
// For multiple chars, builds a union of (str.to_re char) for each char.
func buildCharsetRegex(charset string) string {
	if len(charset) == 0 {
		// Empty charset: matches nothing
		return "re.none"
	}

	runes := []rune(charset)

	if len(runes) == 1 {
		return fmt.Sprintf("(str.to_re \"%s\")", string(runes[0]))
	}

	// Build union of individual character regexes (iterate over runes, not bytes)
	regexes := make([]string, 0, len(runes))
	for _, r := range runes {
		regexes = append(regexes, fmt.Sprintf("(str.to_re \"%s\")", string(r)))
	}

	// Build nested re.union: (re.union r1 (re.union r2 (re.union r3 ...)))
	result := regexes[0]
	for i := 1; i < len(regexes); i++ {
		result = fmt.Sprintf("(re.union %s %s)", result, regexes[i])
	}
	return result
}

// SmtCall generates a SMT representation of call of given function
func (f *Function) SmtCall(params []*SmtValue) (*SmtValue, error) {
	return f.call(params, f.args, f.result)
}

// SmtCallWithConstraints generates the SMT representation of the call and any
// additional top-level constraints (assertions, declarations, etc) associated with the function.
func (f *Function) SmtCallWithConstraints(params []*SmtValue) (*SmtValue, *Bucket, error) {
	callResult, err := f.call(params, f.args, f.result)
	if err != nil {
		return nil, nil, err
	}
	if f.constraints == nil {
		return callResult, nil, nil
	}
	bucket, err := f.constraints(callResult, params, f.args, f.result)
	if err != nil {
		return nil, nil, err
	}
	return callResult, bucket, nil
}

func NewFunctionFromBuiltin(b *ast.Builtin, call callFn) Function {
	bArgs := b.Decl.Args()
	args := make([]ArgType, 0)
	for _, arg := range bArgs {
		args = append(args, NewArgType(arg))
	}
	result := NewArgType(b.Decl.Result())
	return Function{
		args:   args,
		result: result,
		name:   b.Name,
		call:   call,
	}
}

// addBuiltin converts given Builtin into Function and puts it in the funcMap.
func addBuiltin(funcMap map[string]Function, b ast.Builtin, call callFn) {
	f := NewFunctionFromBuiltin(&b, call)
	funcMap[f.name] = f
}

// GetBuiltinFuncMap constructs and returns a map of Rego function converters into SMT.
// This map is accessed via the names of functions, e.g., "plus", "eq".
func GetBuiltinFuncMap() map[string]Function {
	funcMap := make(map[string]Function, 20)
	addBuiltin(funcMap, *ast.Plus, mkSmtFunction("+"))
	addBuiltin(funcMap, *ast.Minus, mkSmtFunction("-"))
	addBuiltin(funcMap, *ast.Multiply, mkSmtFunction("*"))
	addBuiltin(funcMap, *ast.Divide, mkSmtFunction("/"))
	addBuiltin(funcMap, *ast.GreaterThan, mkSmtFunction(">"))
	addBuiltin(funcMap, *ast.GreaterThanEq, mkSmtFunction(">="))
	addBuiltin(funcMap, *ast.LessThan, mkSmtFunction("<"))
	addBuiltin(funcMap, *ast.LessThanEq, mkSmtFunction("<="))
	addBuiltin(funcMap, *ast.Concat, mkSmtFunction("str.++"))
	addBuiltin(funcMap, *ast.Contains, mkSmtFunction("str.contains"))
	addBuiltin(funcMap, *ast.StartsWith, mkSmtFunction("str.prefixof"))
	addBuiltin(funcMap, *ast.EndsWith, mkSmtFunction("str.suffixof"))
	addBuiltin(funcMap, *ast.IndexOf, mkSmtFunction("str.indexof"))
	addBuiltin(funcMap, *ast.Substring, mkSmtFunction("str.substr"))
	addBuiltin(funcMap, *ast.Replace, mkSmtFunction("str.replace_all"))
	trimFunc := NewFunctionFromBuiltin(ast.Trim, TrimFunction)
	trimFunc.constraints = trimConstraints
	funcMap[trimFunc.name] = trimFunc
	// TODO: use define-fun to define lower/upper functions (as nested replace_all)
	// and use these functions to represent ast.Lower and ast.Upper
	addBuiltin(funcMap, *ast.Lower, LowerFunction)
	addBuiltin(funcMap, *ast.Upper, UpperFunction)
	addBuiltin(funcMap, *ast.Equal, EqFunction)
	addBuiltin(funcMap, *ast.Equality, EqFunction)
	addBuiltin(funcMap, *ast.NotEqual, NeqFunction)
	return funcMap
}

// newArgTypeFromTypeDef transforms RegoTypeDef into ArgType.
func newArgTypeFromTypeDef(t types.RegoTypeDef) ArgType {
	return ArgType{
		depth:  t.TypeDepth(),
		atomic: t.AtomicType,
	}
}

// NewFunction notes a user-defined function name of type tp.
func NewFunction(name string, tp types.RegoTypeDef) Function {
	if tp.FunctionDef == nil {
		panic("function type expected")
	}
	args := make([]ArgType, len(tp.FunctionDef.ParamTypes))
	for i, p := range tp.FunctionDef.ParamTypes {
		args[i] = newArgTypeFromTypeDef(p)
	}
	res := newArgTypeFromTypeDef(tp.FunctionDef.ReturnType)
	call := mkSmtFunction(name)
	return Function{name: name, args: args, result: res, call: call}
}
