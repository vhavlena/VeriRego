package model

import (
	"fmt"
	"strconv"
	"strings"

	modelerr "github.com/vhavlena/verirego/pkg/err"
	z3 "github.com/vhavlena/z3-go/z3"
)

// ValueFromSimpleAST converts a Z3 AST that encodes a boolean, integer, or
// string literal into a Value. The helper intentionally keeps the scope narrow
// so that callers can build more complex decoders on top of it.
//
// Parameters:
//
//	ast z3.AST: Literal AST returned by a Z3 model.
//
// Returns:
//
//	Value: Wrapped representation of the literal.
//	error: Failure when the literal uses an unsupported sort or cannot be parsed.
func ValueFromSimpleAST(ast z3.AST) (Value, error) {
	raw := ast.String()
	if raw == "<nil>" || raw == "<invalid>" {
		return Value{}, fmt.Errorf("model: cannot read value from %s AST", raw)
	}

	if numeral := ast.NumeralString(); numeral != "" {
		if strings.Contains(numeral, "/") {
			return Value{}, fmt.Errorf("model: rational numerals (%s) are not supported", numeral)
		}
		intVal, err := strconv.ParseInt(numeral, 10, 64)
		if err != nil {
			return Value{}, fmt.Errorf("model: parse int literal %s: %w", numeral, err)
		}
		return NewIntValue(intVal), nil
	}

	switch raw {
	case "true":
		return NewBoolValue(true), nil
	case "false":
		return NewBoolValue(false), nil
	}

	if len(raw) >= 2 && raw[0] == '"' && raw[len(raw)-1] == '"' {
		unquoted, err := strconv.Unquote(raw)
		if err != nil {
			return Value{}, fmt.Errorf("model: parse string literal %s: %w", raw, err)
		}
		return NewStringValue(unquoted), nil
	}

	return Value{}, fmt.Errorf("%w: %s", modelerr.ErrUnsupportedSimpleValue, raw)
}

// ValueFromOTypeString converts a Z3 AST that inhabits one of the OTypeD sorts
// (see pkg/smt/type_translation.md) into a Value. Only the simple atomic
// constructors (OString, OBoolean, ONumber) are supported for now.
//
// Parameters:
//
//	ast z3.AST: OTypeD AST obtained from a model evaluation.
//
// Returns:
//
//	Value: Go representation of the decoded OType constructor.
//	error: Failure when the constructor is unsupported or malformed.
func ValueFromOTypeString(ast z3.AST) (Value, error) {
	if ast.Kind() == z3.ASTKindUnknown || ast.String() == "<nil>" {
		return Value{}, fmt.Errorf("model: nil OType AST")
	}
	if !ast.IsApp() {
		return Value{}, fmt.Errorf("%w: expected constructor application, got %s", modelerr.ErrUnsupportedOTypeValue, ast.String())
	}
	name := ast.Decl().Name()
	base := strings.TrimRight(name, "0123456789")
	switch base {
	case "Atom":
		if ast.NumChildren() != 1 {
			return Value{}, fmt.Errorf("model: %s expects 1 child, got %d", name, ast.NumChildren())
		}
		return parseOAtomAST(ast.Child(0))
	case "OObj":
		return parseOObjAST(ast)
	case "OArray":
		return Value{}, fmt.Errorf("%w: OArray is not yet supported", modelerr.ErrUnsupportedOTypeValue)
	default:
		// Simplified scheme: atomic values are directly OTypeD0 constructors
		// (OString/ONumber/OBoolean/...) and do not use Atom wrappers.
		if v, atomErr := parseOAtomAST(ast); atomErr == nil {
			return v, nil
		}
		return Value{}, fmt.Errorf("%w: unexpected constructor %s", modelerr.ErrUnsupportedOTypeValue, ast.Decl().Name())
	}
}

// parseOAtomAST converts an OAtom constructor application into a Value.
//
// Parameters:
//
//	ast z3.AST: AST representing the Atom child constructor.
//
// Returns:
//
//	Value: Decoded Value for OString, OBoolean, or ONumber atoms.
//	error: Failure when the constructor is unsupported or ill-formed.
func parseOAtomAST(ast z3.AST) (Value, error) {
	if !ast.IsApp() {
		return Value{}, fmt.Errorf("model: atom field is not constructor application")
	}
	switch ast.Decl().Name() {
	case "OString":
		if ast.NumChildren() != 1 {
			return Value{}, fmt.Errorf("model: OString should expose one child, got %d", ast.NumChildren())
		}
		strVal, ok := ast.Child(0).AsStringLiteral()
		if !ok {
			return Value{}, fmt.Errorf("model: failed to decode string literal from %s", ast.Child(0).String())
		}
		return NewStringValue(strVal), nil
	case "OBoolean":
		if ast.NumChildren() != 1 {
			return Value{}, fmt.Errorf("model: OBoolean should expose one child, got %d", ast.NumChildren())
		}
		boolVal, ok := ast.Child(0).BoolValue()
		if !ok {
			return Value{}, fmt.Errorf("model: failed to decode boolean literal from %s", ast.Child(0).String())
		}
		return NewBoolValue(boolVal), nil
	case "ONumber":
		if ast.NumChildren() != 1 {
			return Value{}, fmt.Errorf("model: ONumber should expose one child, got %d", ast.NumChildren())
		}
		intVal, ok := ast.Child(0).AsInt64()
		if !ok {
			return Value{}, fmt.Errorf("model: failed to decode integer literal from %s", ast.Child(0).String())
		}
		return NewIntValue(intVal), nil
	case "ONull":
		return Value{}, fmt.Errorf("%w: null", modelerr.ErrUnsupportedOTypeValue)
	case "OUndef":
		return Value{}, fmt.Errorf("%w: undef", modelerr.ErrUnsupportedOTypeValue)
	default:
		return Value{}, fmt.Errorf("%w: %s", modelerr.ErrUnsupportedOTypeValue, ast.Decl().Name())
	}
}

// parseOObjAST converts an OObj constructor application into a Value.
//
// Parameters:
//
//	ast z3.AST: AST representing the OObj constructor.
//
// Returns:
//
//	Value: ValueMap with decoded object fields.
//	error: Failure when the structure is invalid or nested decoding fails.
func parseOObjAST(ast z3.AST) (Value, error) {
	if ast.NumChildren() != 1 {
		return Value{}, fmt.Errorf("model: OObj expects 1 child, got %d", ast.NumChildren())
	}
	entries, err := collectStringArrayStores(ast.Child(0))
	if err != nil {
		return Value{}, err
	}
	fields := make(map[string]Value, len(entries))
	for key, valAST := range entries {
		decoded, err := ValueFromOTypeString(valAST)
		if err != nil {
			return Value{}, fmt.Errorf("model: decode object field %s: %w", key, err)
		}
		fields[key] = decoded
	}
	return NewMapValue(fields), nil
}

// collectStringArrayStores traverses a chain of store applications over a
// string-indexed array literal and records the latest AST assigned to each key.
//
// Parameters:
//
//	arrayAST z3.AST: Array literal composed of store/const-array applications.
//
// Returns:
//
//	map[string]z3.AST: Mapping from string keys to value ASTs.
//	error: Failure when non-string keys or unexpected shapes are encountered.
func collectStringArrayStores(arrayAST z3.AST) (map[string]z3.AST, error) {
	if arrayAST.Kind() == z3.ASTKindUnknown {
		return nil, fmt.Errorf("model: invalid array literal in OObj")
	}
	entries := make(map[string]z3.AST)
	cursor := arrayAST
	for cursor.IsApp() && cursor.Decl().Name() == "store" {
		if cursor.NumChildren() != 3 {
			return nil, fmt.Errorf("model: unexpected store arity %d", cursor.NumChildren())
		}
		keyAST := cursor.Child(1)
		key, ok := keyAST.AsStringLiteral()
		if !ok {
			return nil, fmt.Errorf("model: object key is not a string literal: %s", keyAST.String())
		}
		if _, exists := entries[key]; !exists {
			entries[key] = cursor.Child(2)
		}
		cursor = cursor.Child(0)
	}
	if defaultVal, ok := constArrayDefaultValue(cursor); ok {
		entries["*"] = defaultVal
	}
	return entries, nil
}

// constArrayDefaultValue extracts the default element stored in a const-array
// or as-array literal.
//
// Parameters:
//
//	arrayAST z3.AST: AST representing a const-array or as-array application.
//
// Returns:
//
//	z3.AST: Default value stored in the array.
//	bool: True when the array shape is recognized and the value extracted.
func constArrayDefaultValue(arrayAST z3.AST) (z3.AST, bool) {
	if arrayAST.Kind() == z3.ASTKindUnknown {
		return z3.AST{}, false
	}
	if !arrayAST.IsApp() || arrayAST.NumChildren() != 1 {
		return z3.AST{}, false
	}
	switch arrayAST.Decl().Name() {
	case "const-array", "as-array":
		return arrayAST.Child(0), true
	default:
		if strings.Contains(arrayAST.String(), "(as const (Array") {
			return arrayAST.Child(0), true
		}
	}
	return z3.AST{}, false
}
