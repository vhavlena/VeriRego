package types

import "testing"

func TestRegoTypeDefCreation(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		typeDef  RegoTypeDef
		expected struct {
			kind       TypeKind
			atomicType AtomicType
		}
	}{
		{
			name:    "atomic string type",
			typeDef: NewAtomicType(AtomicString),
			expected: struct {
				kind       TypeKind
				atomicType AtomicType
			}{KindAtomic, AtomicString},
		},
		{
			name:    "atomic int type",
			typeDef: NewAtomicType(AtomicInt),
			expected: struct {
				kind       TypeKind
				atomicType AtomicType
			}{KindAtomic, AtomicInt},
		},
		{
			name:    "array type",
			typeDef: NewArrayType(NewAtomicType(AtomicString)),
			expected: struct {
				kind       TypeKind
				atomicType AtomicType
			}{KindArray, ""},
		},
		{
			name: "object type",
			typeDef: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			expected: struct {
				kind       TypeKind
				atomicType AtomicType
			}{KindObject, ""},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			if tt.typeDef.Kind != tt.expected.kind {
				t.Errorf("expected kind %v, got %v", tt.expected.kind, tt.typeDef.Kind)
			}
			if tt.expected.kind == KindAtomic && tt.typeDef.AtomicType != tt.expected.atomicType {
				t.Errorf("expected atomic type %v, got %v", tt.expected.atomicType, tt.typeDef.AtomicType)
			}
		})
	}
}

func TestRegoTypeDefTypeChecks(t *testing.T) {
	t.Parallel()

	// Create test types
	atomicType := NewAtomicType(AtomicString)
	arrayType := NewArrayType(NewAtomicType(AtomicInt))
	objectType := NewObjectType(map[string]RegoTypeDef{
		"field": NewAtomicType(AtomicBoolean),
	})
	unknownType := NewUnknownType()

	// Test IsAtomic
	if !atomicType.IsAtomic() {
		t.Error("atomic type should be identified as atomic")
	}
	if arrayType.IsAtomic() {
		t.Error("array type should not be identified as atomic")
	}

	// Test IsArray
	if !arrayType.IsArray() {
		t.Error("array type should be identified as array")
	}
	if atomicType.IsArray() {
		t.Error("atomic type should not be identified as array")
	}

	// Test IsObject
	if !objectType.IsObject() {
		t.Error("object type should be identified as object")
	}
	if arrayType.IsObject() {
		t.Error("array type should not be identified as object")
	}

	// Test IsUnknown
	if !unknownType.IsUnknown() {
		t.Error("unknown type should be identified as unknown")
	}
	if atomicType.IsUnknown() {
		t.Error("atomic type should not be identified as unknown")
	}
}

func TestRegoTypeDefFieldAccess(t *testing.T) {
	t.Parallel()

	// Test array element type access
	arrayType := NewArrayType(NewAtomicType(AtomicString))
	elemType := arrayType.GetArrayElementType()
	if elemType == nil {
		t.Fatal("expected non-nil array element type")
	}
	if elemType.Kind != KindAtomic || elemType.AtomicType != AtomicString {
		t.Error("unexpected array element type")
	}

	// Test object field access
	objectType := NewObjectType(map[string]RegoTypeDef{
		"field1": NewAtomicType(AtomicString),
		"field2": NewAtomicType(AtomicInt),
	})

	// Test existing field
	field1Type, exists := objectType.GetObjectField("field1")
	if !exists {
		t.Fatal("expected field1 to exist")
	}
	if field1Type.Kind != KindAtomic || field1Type.AtomicType != AtomicString {
		t.Error("unexpected field1 type")
	}

	// Test non-existing field
	_, exists = objectType.GetObjectField("nonexistent")
	if exists {
		t.Error("nonexistent field should not exist")
	}
}

func TestGetTypeFromPath(t *testing.T) {
	t.Parallel()

	// Create a complex nested type for testing
	nestedType := NewObjectType(map[string]RegoTypeDef{
		"users": NewArrayType(NewObjectType(map[string]RegoTypeDef{
			"name":   NewAtomicType(AtomicString),
			"age":    NewAtomicType(AtomicInt),
			"active": NewAtomicType(AtomicBoolean),
			"address": NewObjectType(map[string]RegoTypeDef{
				"street": NewAtomicType(AtomicString),
				"city":   NewAtomicType(AtomicString),
			}),
		})),
		"settings": NewObjectType(map[string]RegoTypeDef{
			"enabled": NewAtomicType(AtomicBoolean),
			"flags":   NewArrayType(NewAtomicType(AtomicString)),
		}),
	})

	tests := []struct {
		name          string
		path          []string
		expectedKind  TypeKind
		expectedType  AtomicType
		shouldSucceed bool
	}{
		{
			name:          "empty path",
			path:          []string{},
			shouldSucceed: false,
		},
		{
			name:          "top level object field",
			path:          []string{"settings"},
			expectedKind:  KindObject,
			shouldSucceed: true,
		},
		{
			name:          "nested atomic field",
			path:          []string{"users", "0", "name"},
			expectedKind:  KindAtomic,
			expectedType:  AtomicString,
			shouldSucceed: true,
		},
		{
			name:          "array type",
			path:          []string{"users"},
			expectedKind:  KindArray,
			shouldSucceed: true,
		},
		{
			name:          "deeply nested field",
			path:          []string{"users", "0", "address", "street"},
			expectedKind:  KindAtomic,
			expectedType:  AtomicString,
			shouldSucceed: true,
		},
		{
			name:          "array of atomic types",
			path:          []string{"settings", "flags", "0"},
			expectedKind:  KindAtomic,
			expectedType:  AtomicString,
			shouldSucceed: true,
		},
		{
			name:          "invalid path",
			path:          []string{"nonexistent"},
			shouldSucceed: false,
		},
		{
			name:          "invalid nested path",
			path:          []string{"users", "0", "nonexistent"},
			shouldSucceed: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, ok := nestedType.GetTypeFromPath(tt.path)

			if tt.shouldSucceed != ok {
				t.Errorf("GetTypeFromPath(%v) success = %v, want %v", tt.path, ok, tt.shouldSucceed)
				return
			}

			if !tt.shouldSucceed {
				if result != nil {
					t.Errorf("GetTypeFromPath(%v) = %v, want nil", tt.path, result)
				}
				return
			}

			if result.Kind != tt.expectedKind {
				t.Errorf("GetTypeFromPath(%v) kind = %v, want %v", tt.path, result.Kind, tt.expectedKind)
			}

			if tt.expectedKind == KindAtomic && result.AtomicType != tt.expectedType {
				t.Errorf("GetTypeFromPath(%v) atomic type = %v, want %v", tt.path, result.AtomicType, tt.expectedType)
			}
		})
	}
}
