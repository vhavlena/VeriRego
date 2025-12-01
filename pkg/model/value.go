package model

// ValueKind enumerates the supported Go-style value categories that can be
// extracted from a Z3 model.
//
// Values:
//
//	ValueInvalid | ValueBool | ValueInt | ValueString | ValueArray | ValueMap
type ValueKind string

const (
	ValueInvalid ValueKind = "invalid"
	ValueBool    ValueKind = "bool"
	ValueInt     ValueKind = "int"
	ValueString  ValueKind = "string"
	ValueArray   ValueKind = "array"
	ValueMap     ValueKind = "map"
)

// wildcardKey represents the default element stored in Z3 const-array models.
const wildcardKey = "*"

// Value is a simple tagged-union that allows callers to inspect model results
// without dealing with raw Z3 AST handles.
//
// Fields:
//
//	kind ValueKind: Discriminator.
//	boolVal bool: Payload for bool values.
//	intVal int64: Payload for integers.
//	stringVal string: Payload for strings.
//	arrayVal []Value: Payload for arrays.
//	mapVal map[string]Value: Payload for maps.
type Value struct {
	kind      ValueKind
	boolVal   bool
	intVal    int64
	stringVal string
	arrayVal  []Value
	mapVal    map[string]Value
}

// NewBoolValue creates a Value that stores a boolean.
//
// Parameters:
//
//	v bool: Boolean payload to wrap.
//
// Returns:
//
//	Value: A Value tagged as ValueBool.
func NewBoolValue(v bool) Value {
	return Value{kind: ValueBool, boolVal: v}
}

// NewIntValue creates a Value that stores a signed integer.
//
// Parameters:
//
//	v int64: Numeric payload to wrap.
//
// Returns:
//
//	Value: A Value tagged as ValueInt.
func NewIntValue(v int64) Value {
	return Value{kind: ValueInt, intVal: v}
}

// NewStringValue creates a Value that stores a UTF-8 string.
//
// Parameters:
//
//	v string: String payload to wrap.
//
// Returns:
//
//	Value: A Value tagged as ValueString.
func NewStringValue(v string) Value {
	return Value{kind: ValueString, stringVal: v}
}

// NewArrayValue creates a Value that stores an ordered collection.
//
// Parameters:
//
//	items []Value: Elements of the resulting array.
//
// Returns:
//
//	Value: A Value tagged as ValueArray with a defensive copy of items.
func NewArrayValue(items []Value) Value {
	cp := make([]Value, len(items))
	copy(cp, items)
	return Value{kind: ValueArray, arrayVal: cp}
}

// NewMapValue creates a Value that stores a string-keyed map.
//
// Parameters:
//
//	entries map[string]Value: Map entries to clone.
//
// Returns:
//
//	Value: A Value tagged as ValueMap with copied entries.
func NewMapValue(entries map[string]Value) Value {
	cp := make(map[string]Value, len(entries))
	for k, v := range entries {
		cp[k] = v
	}
	return Value{kind: ValueMap, mapVal: cp}
}

// Kind returns the discriminator for the stored data.
//
// Returns:
//
//	ValueKind: The stored kind, defaulting to ValueInvalid when unset.
func (v Value) Kind() ValueKind {
	if v.kind == "" {
		return ValueInvalid
	}
	return v.kind
}

// Bool returns the boolean payload when the Value represents a bool.
//
// Returns:
//
//	bool: Stored boolean value.
//	bool: True when the Value actually contains a boolean.
func (v Value) Bool() (bool, bool) {
	if v.kind != ValueBool {
		return false, false
	}
	return v.boolVal, true
}

// Int64 returns the integer payload when the Value represents an int.
//
// Returns:
//
//	int64: Stored integer value.
//	bool: True when the Value actually contains an integer.
func (v Value) Int64() (int64, bool) {
	if v.kind != ValueInt {
		return 0, false
	}
	return v.intVal, true
}

// String returns the string payload when the Value represents a string.
//
// Returns:
//
//	string: Stored string value.
//	bool: True when the Value actually contains a string.
func (v Value) String() (string, bool) {
	if v.kind != ValueString {
		return "", false
	}
	return v.stringVal, true
}

// Array returns the slice payload when the Value represents an array.
//
// Returns:
//
//	[]Value: Defensive copy of the stored slice.
//	bool: True when the Value actually contains an array.
func (v Value) Array() ([]Value, bool) {
	if v.kind != ValueArray {
		return nil, false
	}
	cp := make([]Value, len(v.arrayVal))
	copy(cp, v.arrayVal)
	return cp, true
}

// Map returns the map payload when the Value represents an object.
//
// Returns:
//
//	map[string]Value: Defensive copy of the stored map.
//	bool: True when the Value actually contains a map.
func (v Value) Map() (map[string]Value, bool) {
	if v.kind != ValueMap {
		return nil, false
	}
	cp := make(map[string]Value, len(v.mapVal))
	for k, val := range v.mapVal {
		cp[k] = val
	}
	return cp, true
}

// AsInterface returns the closest built-in Go representation (bool, string,
// int64, []any, map[string]any) for the stored value, recursively converting
// nested elements.
//
// Returns:
//
//	any: Native Go value matching the stored payload.
func (v Value) AsInterface() any {
	switch v.kind {
	case ValueBool:
		return v.boolVal
	case ValueInt:
		return v.intVal
	case ValueString:
		return v.stringVal
	case ValueArray:
		arr := make([]any, len(v.arrayVal))
		for i, item := range v.arrayVal {
			arr[i] = item.AsInterface()
		}
		return arr
	case ValueMap:
		mp := make(map[string]any, len(v.mapVal))
		for k, item := range v.mapVal {
			mp[k] = item.AsInterface()
		}
		return mp
	default:
		return nil
	}
}

// Equal performs a deep comparison between two Values, taking into account the
// wildcard semantics used by Z3 const-array models (key "*").
func (v Value) Equal(other Value) bool {
	if v.Kind() != other.Kind() {
		return false
	}
	switch v.Kind() {
	case ValueInvalid:
		return true
	case ValueBool:
		return v.boolVal == other.boolVal
	case ValueInt:
		return v.intVal == other.intVal
	case ValueString:
		return v.stringVal == other.stringVal
	case ValueArray:
		if len(v.arrayVal) != len(other.arrayVal) {
			return false
		}
		for i := range v.arrayVal {
			if !v.arrayVal[i].Equal(other.arrayVal[i]) {
				return false
			}
		}
		return true
	case ValueMap:
		return mapEqualWithWildcard(v.mapVal, other.mapVal)
	default:
		return false
	}
}

func mapEqualWithWildcard(a, b map[string]Value) bool {
	for key, val := range a {
		if key == wildcardKey {
			continue
		}
		otherVal, ok := mapLookupWithWildcard(b, key)
		if !ok || !val.Equal(otherVal) {
			return false
		}
	}
	for key, val := range b {
		if key == wildcardKey {
			continue
		}
		otherVal, ok := mapLookupWithWildcard(a, key)
		if !ok || !val.Equal(otherVal) {
			return false
		}
	}
	wildA, hasWildA := a[wildcardKey]
	wildB, hasWildB := b[wildcardKey]
	if hasWildA && hasWildB {
		return wildA.Equal(wildB)
	}
	return true
}

func mapLookupWithWildcard(m map[string]Value, key string) (Value, bool) {
	if m == nil {
		return Value{}, false
	}
	if v, ok := m[key]; ok {
		return v, true
	}
	if wildcard, ok := m[wildcardKey]; ok {
		return wildcard, true
	}
	return Value{}, false
}
