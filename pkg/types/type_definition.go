// Package types provides type analysis for Rego AST.
package types

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
func (t RegoTypeDef) IsAtomic() bool {
	return t.Kind == KindAtomic
}

// IsArray returns true if the type is an array
func (t RegoTypeDef) IsArray() bool {
	return t.Kind == KindArray
}

// IsObject returns true if the type is an object
func (t RegoTypeDef) IsObject() bool {
	return t.Kind == KindObject
}

// IsUnknown returns true if the type is unknown
func (t RegoTypeDef) IsUnknown() bool {
	return t.Kind == KindUnknown
}

// GetArrayElementType returns the type of array elements
// Returns nil if the type is not an array
func (t RegoTypeDef) GetArrayElementType() *RegoTypeDef {
	if !t.IsArray() {
		return nil
	}
	return t.ArrayType
}

// GetObjectField returns the type of a field in an object
// Returns (nil, false) if the field doesn't exist or if the type is not an object
func (t RegoTypeDef) GetObjectField(field string) (*RegoTypeDef, bool) {
	if !t.IsObject() {
		return nil, false
	}
	fieldType, exists := t.ObjectFields[field]
	if !exists {
		return nil, false
	}
	return &fieldType, true
}

// GetTypeFromPath returns the type at the given path in an object or array structure.
// For arrays, all indices are treated as having the same type.
// Returns (nil, false) if:
// - The current type is not an object or array
// - The path is invalid (key doesn't exist in object)
// - The path is empty
func (t RegoTypeDef) GetTypeFromPath(path []string) (*RegoTypeDef, bool) {
	if len(path) == 0 {
		return nil, false
	}

	currentKey := path[0]
	remainingPath := path[1:]

	switch t.Kind {
	case KindObject:
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
		// For arrays, we ignore the actual index since all elements have the same type
		if len(remainingPath) == 0 {
			return t.ArrayType, true
		}
		return t.ArrayType.GetTypeFromPath(remainingPath)

	default:
		return nil, false
	}
}

// FromRegoType converts a RegoType to a RegoTypeDef
func FromRegoType(typ RegoType) RegoTypeDef {
	switch typ {
	case TypeString:
		return NewAtomicType(AtomicString)
	case TypeInt:
		return NewAtomicType(AtomicInt)
	case TypeBoolean:
		return NewAtomicType(AtomicBoolean)
	case TypeFunction:
		return NewAtomicType(AtomicFunction)
	case TypeSet:
		return NewAtomicType(AtomicSet)
	case TypeArray:
		return NewArrayType(NewUnknownType()) // Default to unknown element type
	case TypeObject:
		return NewObjectType(make(map[string]RegoTypeDef))
	default:
		return NewUnknownType()
	}
}

// ToRegoType converts a RegoTypeDef to a RegoType
func (t RegoTypeDef) ToRegoType() RegoType {
	switch t.Kind {
	case KindAtomic:
		switch t.AtomicType {
		case AtomicString:
			return TypeString
		case AtomicInt:
			return TypeInt
		case AtomicBoolean:
			return TypeBoolean
		case AtomicFunction:
			return TypeFunction
		case AtomicSet:
			return TypeSet
		}
	case KindArray:
		return TypeArray
	case KindObject:
		return TypeObject
	}
	return TypeUnknown
}
