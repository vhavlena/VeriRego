package smt

import (
	"fmt"
	"strings"
	"unicode"

	"github.com/open-policy-agent/opa/v1/ast"
	ast_types "github.com/open-policy-agent/opa/v1/types"
	verr "github.com/vhavlena/verirego/pkg/err"
	types "github.com/vhavlena/verirego/pkg/types"
)

// UseUnicodeCase controls whether to_lower/to_upper should operate on full Unicode
// or only ASCII. Default is false (ASCII-only behavior).
var UseUnicodeCase bool = false

// SetUseUnicodeCase sets the package-wide flag controlling case handling.
func SetUseUnicodeCase(v bool) {
	UseUnicodeCase = v
}

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

// substrConstraints generates constraints for substr(s, i, j):
// if j < 0: result = str.substr(s, i, str.len(s))
// else: result = str.substr(s, i, j)
// TODO: if i < 0, we should return undef, not possible for now
var substrConstraints constraintsFn = func(callResult *SmtValue, params []*SmtValue, args []ArgType, result ArgType) (*Bucket, error) {
	bucket := NewBucket()
	if len(params) != 3 {
		return nil, verr.ErrUnexpectedParamCount("substr", 3, len(params))
	}

	s, err := params[0].AsString()
	if err != nil {
		return nil, err
	}
	i, err := params[1].AsInt()
	if err != nil {
		return nil, err
	}
	j := params[2]

	// Build: if (< j 0) then (str.substr s i (str.len s)) else (str.substr s i j)
	lenS := fmt.Sprintf("(str.len %s)", s.String())
	correctNegative := fmt.Sprintf("(str.substr %s %s %s)", s.String(), i.String(), lenS)
	correctNonNeg := fmt.Sprintf("(str.substr %s %s %s)", s.String(), i.String(), j.String())
	iteExpr := fmt.Sprintf("(ite (< %s 0) %s %s)", j.String(), correctNegative, correctNonNeg)
	eqVal := fmt.Sprintf("(= %s %s)", callResult.String(), iteExpr)
	bucket.Asserts = append(bucket.Asserts, Assert(RawProposition(eqVal)))
	return bucket, nil
}

// trimConstraints generates SMT constraints about the trim operation.
// trim_left - whether to trim from left
// trim_right - whether to trim from right
// both directions can be true (then we trim from both sides)
func trimConstraints(trim_left bool, trim_right bool) constraintsFn {
	res := func(callResult *SmtValue, params []*SmtValue, args []ArgType, result ArgType) (*Bucket, error) {
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

		// General case for (trim x chars)

		if !params[1].isConst || !params[1].TypeIs(types.AtomicString) {
			return nil, verr.ErrNotImplemented("trim with second argument that is not literal")
		}

		// get raw input string expression
		inputStr, err := params[0].AsString()
		if err != nil {
			return nil, err
		}

		// Build regex representing the set C of chars (union of each char)
		cRegex, err := buildCharsetRegex(params[1].value)
		if err != nil {
			return nil, err
		}
		// Build the set of all chars outside of C: (S/C) = re.diff re.allchar C
		notCRegex := fmt.Sprintf("(re.diff re.allchar %s)", cRegex)
		// Build C* and (S/C)*
		cStar := fmt.Sprintf("(re.* %s)", cRegex)
		notCStar := fmt.Sprintf("(re.* %s)", notCRegex)

		// General case: assert existence of fresh y,z (strings) such that
		// (= x (str.++ y (trim x chars) z))
		// where y is there only if trim_left is true, z is there only if trim_right is true
		y := RandString(8)
		z := RandString(8)
		partsOfRightSide := []string{}

		if trim_left {
			// declare y as a string var
			bucket.Decls = append(bucket.Decls, RawCommand(fmt.Sprintf("(declare-const %s String)", y)))
			// Assert y in C*
			bucket.Asserts = append(bucket.Asserts, Assert(RawProposition(fmt.Sprintf("(str.in_re %s %s)", y, cStar))))
			// add y to the right side of the equation
			partsOfRightSide = append(partsOfRightSide, y)
		}

		// add (trim x chars) to the right side of the equation
		partsOfRightSide = append(partsOfRightSide, callResult.String())

		if trim_right {
			// declare z as a string var
			bucket.Decls = append(bucket.Decls, RawCommand(fmt.Sprintf("(declare-const %s String)", z)))
			// Assert z in C*
			bucket.Asserts = append(bucket.Asserts, Assert(RawProposition(fmt.Sprintf("(str.in_re %s %s)", z, cStar))))
			// add z to the right side of the equation
			partsOfRightSide = append(partsOfRightSide, z)
		}

		// (= x (str.++ y (trim x chars) z))
		concat := fmt.Sprintf("(str.++ %s)", strings.Join(partsOfRightSide, " "))
		eqVal := fmt.Sprintf("(= %s %s)", inputStr.String(), concat)
		bucket.Asserts = append(bucket.Asserts, Assert(RawProposition(eqVal)))

		// Assert (trim x chars) in (S/C)* + (S/C).S*.(S/C)
		// but in (S/C).S*.(S/C), the first (S/C) is there only if trim_left is true
		// and the second (S/C) is there only if trim_right is true
		secondConcatParts := []string{}
		if trim_left {
			secondConcatParts = append(secondConcatParts, notCRegex)
		}
		secondConcatParts = append(secondConcatParts, "re.all")
		if trim_right {
			secondConcatParts = append(secondConcatParts, notCRegex)
		}
		secondConcat := fmt.Sprintf("(re.++ %s)", strings.Join(secondConcatParts, " "))
		trimResultRegex := fmt.Sprintf("(re.union %s %s)", notCStar, secondConcat)
		bucket.Asserts = append(bucket.Asserts,
			Assert(RawProposition(fmt.Sprintf("(str.in_re %s %s)", callResult.String(), trimResultRegex))))

		return bucket, nil
	}
	return res
}

// buildCharsetRegex builds an SMT regex that matches any single character in the charset.
// For empty charset, returns re.none. For single char, returns (str.to_re char).
// For multiple chars, builds a union of (str.to_re char) for each char.
func buildCharsetRegex(smtString string) (string, error) {
	// Optional surrounding quotes.
	if len(smtString) >= 2 && smtString[0] == '"' && smtString[len(smtString)-1] == '"' {
		smtString = smtString[1 : len(smtString)-1]
	}

	chars := make([]string, 0, len(smtString))
	for i := 0; i < len(smtString); {
		if smtString[i] != '\\' {
			chars = append(chars, string(smtString[i])) // literal ASCII byte
			i++
			continue
		}

		// Must be \u{...}
		if i+3 >= len(smtString) || smtString[i+1] != 'u' || smtString[i+2] != '{' {
			return "", fmt.Errorf("invalid escape at byte %d", i)
		}

		j := i + 3
		for j < len(smtString) && smtString[j] != '}' {
			j++
		}
		if j >= len(smtString) || smtString[j] != '}' {
			return "", fmt.Errorf("unterminated \\u{...} escape at byte %d", i)
		}

		chars = append(chars, smtString[i:j+1])
		i = j + 1
	}

	if len(chars) == 0 {
		return "re.none", nil
	}

	// Build union of individual character regexes (iterate over runes, not bytes)
	regexes := make([]string, 0, len(chars))
	for _, char := range chars {
		regexes = append(regexes, fmt.Sprintf("(str.to_re \"%s\")", string(char)))
	}

	// Build nested re.union: (re.union r1 (re.union r2 (re.union r3 ...)))
	result := regexes[0]
	for i := 1; i < len(regexes); i++ {
		result = fmt.Sprintf("(re.union %s %s)", result, regexes[i])
	}
	return result, nil
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
func addBuiltinWithConstraints(funcMap map[string]Function, b ast.Builtin, call callFn, constraints constraintsFn) {
	f := NewFunctionFromBuiltin(&b, call)
	f.constraints = constraints
	funcMap[f.name] = f
}

func addBuiltin(funcMap map[string]Function, b ast.Builtin, call callFn) {
	addBuiltinWithConstraints(funcMap, b, call, nil)
}

// GetBuiltinFuncMap constructs and returns a map of Rego function converters into SMT.
// This map is accessed via the names of functions, e.g., "plus", "eq".
// See also GetBuiltinDecls()
func GetBuiltinFuncMap() map[string]Function {
	funcMap := make(map[string]Function, 20)

	addBuiltin(funcMap, *ast.Equal, EqFunction)
	addBuiltin(funcMap, *ast.Equality, EqFunction)
	addBuiltin(funcMap, *ast.NotEqual, NeqFunction)

	// builtin functions with counterparts in SMT
	addBuiltin(funcMap, *ast.Plus, mkSmtFunction("+"))
	addBuiltin(funcMap, *ast.Minus, mkSmtFunction("-"))
	addBuiltin(funcMap, *ast.Multiply, mkSmtFunction("*"))
	addBuiltin(funcMap, *ast.Divide, mkSmtFunction("/"))
	addBuiltin(funcMap, *ast.GreaterThan, mkSmtFunction(">"))
	addBuiltin(funcMap, *ast.GreaterThanEq, mkSmtFunction(">="))
	addBuiltin(funcMap, *ast.LessThan, mkSmtFunction("<"))
	addBuiltin(funcMap, *ast.LessThanEq, mkSmtFunction("<="))
	// addBuiltin(funcMap, *ast.Concat, mkSmtFunction("str.++")) // TODO incorrect, ast.Concat has different semantics than str.++
	addBuiltin(funcMap, *ast.Contains, mkSmtFunction("str.contains"))
	addBuiltin(funcMap, *ast.StartsWith, mkSmtFunction("str.prefixof"))
	addBuiltin(funcMap, *ast.EndsWith, mkSmtFunction("str.suffixof"))
	addBuiltin(funcMap, *ast.IndexOf, mkSmtFunction("str.indexof"))
	addBuiltin(funcMap, *ast.Replace, mkSmtFunction("str.replace_all"))

	// builtin functions without counterparts, they use newly declared/defined SMT functions (see GetBuiltinDecls())
	addBuiltinWithConstraints(funcMap, *ast.Substring, mkSmtFunction("__substr"), substrConstraints) // we cannot use str.substr directly, third argument (length) behaves differently for negative numbers
	addBuiltinWithConstraints(funcMap, *ast.Trim, mkSmtFunction("__trim"), trimConstraints(true, true))
	addBuiltinWithConstraints(funcMap, *ast.TrimLeft, mkSmtFunction("__trim_left"), trimConstraints(true, false))
	addBuiltinWithConstraints(funcMap, *ast.TrimRight, mkSmtFunction("__trim_right"), trimConstraints(false, true))
	addBuiltin(funcMap, *ast.Lower, mkSmtFunction("__to_lower"))
	addBuiltin(funcMap, *ast.Upper, mkSmtFunction("__to_upper"))

	return funcMap
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

func generateCaseTemplateUnicode(lower bool) string {
	template := "%s"
	for r := rune(0); r <= unicode.MaxRune; r++ {
		// Skip surrogate code points (invalid Unicode scalars)
		if r >= 0xD800 && r <= 0xDFFF {
			continue
		}

		var c rune
		if lower {
			c = unicode.ToLower(r)
		} else {
			c = unicode.ToUpper(r)
		}

		// Only print runes that actually change
		if c != r {
			template = fmt.Sprintf(`(str.replace_all %s "%s" "%s")`, template, SmtCharFromRune(r), SmtCharFromRune(c))
		}
	}
	return template
}

// Creates function declarations/definitions used for built in Rego functions (see also GetBuilinFuncMap())
func GetBuiltinDecls() []*SmtCommand {
	res := make([]*SmtCommand, 0, 64)
	res = append(res, DeclareFun("__substr", []string{"String", "Int", "Int"}, "String"))
	res = append(res, DeclareFun("__trim", []string{"String", "String"}, "String"))
	res = append(res, DeclareFun("__trim_left", []string{"String", "String"}, "String"))
	res = append(res, DeclareFun("__trim_right", []string{"String", "String"}, "String"))
	// Define case functions depending on configured behavior.
	if UseUnicodeCase {
		// Unicode-aware implementation will be provided by caller later.
		// For now, keep same define-fun placeholder; user can replace body.
		res = append(res, &SmtCommand{value: fmt.Sprintf("(define-fun __to_upper ((x String)) String %s)", fmt.Sprintf(generateCaseTemplateUnicode(false), "x"))})
		res = append(res, &SmtCommand{value: fmt.Sprintf("(define-fun __to_lower ((x String)) String %s)", fmt.Sprintf(generateCaseTemplateUnicode(true), "x"))})
	} else {
		// ASCII-only implementation using nested str.replace_all templates.
		res = append(res, &SmtCommand{value: fmt.Sprintf("(define-fun __to_upper ((x String)) String %s)", fmt.Sprintf(toUpperTemplate, "x"))})
		res = append(res, &SmtCommand{value: fmt.Sprintf("(define-fun __to_lower ((x String)) String %s)", fmt.Sprintf(toLowerTemplate, "x"))})
	}
	return res
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
