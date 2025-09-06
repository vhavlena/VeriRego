// Package types provides type analysis for Rego AST.
package types

import (
	"github.com/open-policy-agent/opa/ast"
)

// TypeKind represents the kind of a Rego type
type TypeKind string

const (
	KindAtomic  TypeKind = "atomic"
	KindArray   TypeKind = "array"
	KindObject  TypeKind = "object"
	KindUnknown TypeKind = "unknown"
)

// AtomicType represents atomic types in Rego
type AtomicType string

const (
	AtomicString   AtomicType = "string"
	AtomicInt      AtomicType = "int"
	AtomicBoolean  AtomicType = "boolean"
	AtomicFunction AtomicType = "function"
	AtomicSet      AtomicType = "set"
)

// RegoTypeDef represents a full type definition in Rego
type RegoTypeDef struct {
	Kind         TypeKind               // The kind of type (atomic, array, object)
	AtomicType   AtomicType             // The specific atomic type if Kind is atomic
	ArrayType    *RegoTypeDef           // The type of array elements if Kind is array
	ObjectFields map[string]RegoTypeDef // The field types if Kind is object
}

//----------------------------------------------------------------

type PathNode struct {
	Key      string
	IsGround bool // Ground = constant, non-ground = variable
}

func FromGroundPath(path []string) []PathNode {
	nodes := make([]PathNode, len(path))
	for i, p := range path {
		nodes[i] = PathNode{
			Key:      p,
			IsGround: true,
		}
	}
	return nodes
}

func FromRef(ref ast.Ref) []PathNode {
	path := make([]PathNode, 0, len(ref))
	for _, term := range ref {
		if str, ok := term.Value.(ast.String); ok {
			path = append(path, PathNode{
				Key:      string(str),
				IsGround: true,
			})
		} else {
			path = append(path, PathNode{
				Key:      term.String(),
				IsGround: term.Value.IsGround(),
			})
		}
	}
	return path
}

//----------------------------------------------------------------

// NewAtomicType creates a new RegoTypeDef for an atomic type
func NewAtomicType(atomicType AtomicType) RegoTypeDef {
	return RegoTypeDef{
		Kind:       KindAtomic,
		AtomicType: atomicType,
	}
}

// NewArrayType creates a new RegoTypeDef for an array type
func NewArrayType(elementType RegoTypeDef) RegoTypeDef {
	return RegoTypeDef{
		Kind:      KindArray,
		ArrayType: &elementType,
	}
}

// NewObjectType creates a new RegoTypeDef for an object type
func NewObjectType(fields map[string]RegoTypeDef) RegoTypeDef {
	return RegoTypeDef{
		Kind:         KindObject,
		ObjectFields: fields,
	}
}

// NewUnknownType creates a new RegoTypeDef for an unknown type
func NewUnknownType() RegoTypeDef {
	return RegoTypeDef{
		Kind: KindUnknown,
	}
}

// IsAtomic returns true if the type is atomic
func (t *RegoTypeDef) IsAtomic() bool {
	return t.Kind == KindAtomic
}

// IsArray returns true if the type is an array
func (t *RegoTypeDef) IsArray() bool {
	return t.Kind == KindArray
}

// IsObject returns true if the type is an object
func (t *RegoTypeDef) IsObject() bool {
	return t.Kind == KindObject
}

// IsUnknown returns true if the type is unknown
func (t *RegoTypeDef) IsUnknown() bool {
	return t.Kind == KindUnknown
}

// GetArrayElementType returns the type of array elements
// Returns nil if the type is not an array
func (t *RegoTypeDef) GetArrayElementType() *RegoTypeDef {
	if !t.IsArray() {
		return nil
	}
	return t.ArrayType
}

// GetObjectField returns the type of a field in an object
// Returns (nil, false) if the field doesn't exist or if the type is not an object
func (t *RegoTypeDef) GetObjectField(field string) (*RegoTypeDef, bool) {
	if !t.IsObject() {
		return nil, false
	}
	fieldType, exists := t.ObjectFields[field]
	if !exists {
		return nil, false
	}
	return &fieldType, true
}

// IsEqual checks if this type is exactly equal to another type
func (t *RegoTypeDef) IsEqual(other *RegoTypeDef) bool {
	if t.Kind != other.Kind {
		return false
	}

	switch t.Kind {
	case KindAtomic:
		return t.AtomicType == other.AtomicType
	case KindArray:
		if t.ArrayType == nil || other.ArrayType == nil {
			return t.ArrayType == other.ArrayType
		}
		return t.ArrayType.IsEqual(other.ArrayType)
	case KindObject:
		if len(t.ObjectFields) != len(other.ObjectFields) {
			return false
		}
		for field, type1 := range t.ObjectFields {
			type2, exists := other.ObjectFields[field]
			if !exists || !type1.IsEqual(&type2) {
				return false
			}
		}
		return true
	case KindUnknown:
		return true
	}
	return false
}

// compareObjects checks if the current object type is more precise than another object type.
//
// Parameters:
//
//	other *RegoTypeDef: The other object type to compare against.
//
// Returns:
//
//	bool: True if the current object type is more precise
func (t *RegoTypeDef) compareObjects(other *RegoTypeDef) bool {
	// Must have at least as many fields as other
	if len(t.ObjectFields) < len(other.ObjectFields) {
		return false
	}

	// Check common fields recursively
	for fieldName, otherType := range other.ObjectFields {
		thisType, exists := t.ObjectFields[fieldName]
		if !exists {
			return false
		}
		// For common fields, this type should be at least as precise
		if !thisType.IsMorePrecise(&otherType) && !thisType.IsEqual(&otherType) {
			return false
		}
	}

	// Must have strictly more fields or equal fields with at least one being more precise
	return len(t.ObjectFields) > len(other.ObjectFields) || hasMorePreciseField(t, other)
}

// hasMorePreciseField checks if any field in t1 is more precise than the corresponding field in t2
func hasMorePreciseField(t1, t2 *RegoTypeDef) bool {
	for fieldName, type1 := range t1.ObjectFields {
		type2, exists := t2.ObjectFields[fieldName]
		if !exists {
			continue
		}
		if type1.IsMorePrecise(&type2) {
			return true
		}
	}
	return false
}

// IsMorePrecise returns true if this type is more precise than the other type.
// An atomic type is more precise than non-atomic types.
// For objects, having more fields (recursively) means more precise.
// For arrays, having more precise element type means more precise.
func (t *RegoTypeDef) IsMorePrecise(other *RegoTypeDef) bool {
	if t.IsUnknown() {
		return false
	}
	if other.IsUnknown() {
		return true
	}
	if t.Kind != other.Kind {
		return t.IsAtomic()
	}

	switch t.Kind {
	case KindAtomic:
		return false // equal precision, not more precise
	case KindArray:
		if t.ArrayType == nil || other.ArrayType == nil {
			return false
		}
		return t.ArrayType.IsMorePrecise(other.ArrayType)
	case KindObject:
		return t.compareObjects(other)
	case KindUnknown:
		return false
	}
	return false
}

// GetTypeFromPath walks the type definition following the provided path of PathNode
// values and returns the resolved type if it can be determined.
//
// Behavior summary:
// - An empty path returns the receiver type.
// - For object types:
//   - If the current path node is ground (IsGround == true) the named field is looked up.
//   - If the current path node is non-ground (variable) the method will only succeed
//     if all object field types are identical; in that case traversal continues using
//     the common field type. If field types differ, the type cannot be determined.
//   - For array types any index (ground or non-ground) resolves to the array element type
//     and traversal continues on that element type.
//   - For atomic or unknown kinds traversal cannot continue and the function returns
//     (nil, false).
//
// The boolean return value is true when a deterministic type was found for the full
// path, and false otherwise.
func (t *RegoTypeDef) GetTypeFromPath(path []PathNode) (*RegoTypeDef, bool) {
	if len(path) == 0 {
		return t, true
	}

	currentKey := path[0].Key
	remainingPath := path[1:]

	switch t.Kind {
	case KindObject:
		// for non-ground keys (= variables), we need to check all values for all
		// keys have the same type. If not, we cannot determine the type.
		if !path[0].IsGround {
			if len(t.ObjectFields) == 0 {
				return nil, false
			}
			var allFieldType *RegoTypeDef
			for _, v := range t.ObjectFields {
				if allFieldType == nil {
					allFieldType = &v
				} else {
					if !allFieldType.IsEqual(&v) {
						return nil, false // Different field types, cannot determine
					}
				}
			}
			return allFieldType.GetTypeFromPath(remainingPath)
		}

		fieldType, exists := t.ObjectFields[currentKey]
		if !exists {
			return nil, false
		}
		if len(remainingPath) == 0 {
			return &fieldType, true
		}
		return fieldType.GetTypeFromPath(remainingPath)
	case KindArray:
		if t.ArrayType == nil {
			return nil, false
		}
		if len(remainingPath) == 0 {
			return t.ArrayType, true
		}
		return t.ArrayType.GetTypeFromPath(remainingPath)
	case KindAtomic, KindUnknown:
		return nil, false
	}
	return nil, false
}

// PrettyPrintShort returns a human-readable string representation of the RegoTypeDef.
//
// Returns:
//
//	string: The pretty-printed type definition.
func (t *RegoTypeDef) PrettyPrintShort() string {
	return t.prettyPrintWithIndentShort(0, true)
}

// PrettyPrint returns a human-readable string representation of the RegoTypeDef.
// This is equivalent to PrettyPrintShort(false).
//
// Returns:
//
//	string: The pretty-printed type definition.
func (t *RegoTypeDef) PrettyPrint() string {
	return t.prettyPrintWithIndentShort(0, false)
}

// prettyPrintWithIndentShort is a helper for pretty printing with indentation and short mode.
//
// Parameters:
//
//	indent int: The indentation level.
//	short bool: If true, object types are shown as just "object".
//
// Returns:
//
//	string: The pretty-printed type definition with indentation.
func (t *RegoTypeDef) prettyPrintWithIndentShort(indent int, short bool) string {
	spaces := "  "
	ind := ""
	for i := 0; i < indent; i++ {
		ind += spaces
	}
	switch t.Kind {
	case KindAtomic:
		return string(t.AtomicType)
	case KindArray:
		if t.ArrayType == nil {
			return "array<unknown>"
		}
		return "array<" + t.ArrayType.prettyPrintWithIndentShort(indent, short) + ">"
	case KindObject:
		if short {
			return "object"
		}
		if len(t.ObjectFields) == 0 {
			return "object{}"
		}
		result := "object{\n"
		for k, v := range t.ObjectFields {
			result += ind + spaces + k + ": " + v.prettyPrintWithIndentShort(indent+1, short) + "\n"
		}
		result += ind + "}"
		return result
	case KindUnknown:
		return "unknown"
	}
	return "invalid"
}

// TypeMapEqual returns true if two type maps are deeply equal.
//
// Parameters:
//
//	a map[string]RegoTypeDef: The first type map to compare.
//	b map[string]RegoTypeDef: The second type map to compare.
//
// Returns:
//
//	bool: True if the type maps are equal
func TypeMapEqual(a, b map[string]RegoTypeDef) bool {
	if len(a) != len(b) {
		return false
	}
	for k, v := range a {
		bv, ok := b[k]
		if !ok || !v.IsEqual(&bv) {
			return false
		}
	}
	return true
}

// CopyTypeMap returns a deep copy of a type map.
//
// Parameters:
//
//	src map[string]RegoTypeDef: The source type map to copy.
//
// Returns:
//
//	map[string]RegoTypeDef: A new map containing the copied types.
func CopyTypeMap(src map[string]RegoTypeDef) map[string]RegoTypeDef {
	cp := make(map[string]RegoTypeDef)
	for k, v := range src {
		cp[k] = v // RegoTypeDef is a struct, so this is a deep copy unless it contains pointers
	}
	return cp
}

// TypeDepth computes the depth of the datatype.
//
// Returns:
//
//	int: The depth of the type. For atomic and unknown types, the depth is 1. For arrays and objects, it is 1 plus the maximum depth of nested types.
func (t *RegoTypeDef) TypeDepth() int {
	switch t.Kind {
	case KindAtomic, KindUnknown:
		return 0
	case KindArray:
		if t.ArrayType == nil {
			return 1
		}
		return 1 + t.ArrayType.TypeDepth()
	case KindObject:
		maxDepth := 0
		for _, fieldType := range t.ObjectFields {
			depth := fieldType.TypeDepth()
			if depth > maxDepth {
				maxDepth = depth
			}
		}
		return 1 + maxDepth
	}
	return 0
}
