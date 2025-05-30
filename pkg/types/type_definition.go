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

func (t *RegoTypeDef) GetTypeFromPath(path []string) (*RegoTypeDef, bool) {
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
		if len(remainingPath) == 0 {
			return t.ArrayType, true
		}
		return t.ArrayType.GetTypeFromPath(remainingPath)
	case KindAtomic, KindUnknown:
		return nil, false
	}
	return nil, false
}
