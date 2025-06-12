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
			shouldSucceed: true,
			expectedKind:  KindObject,
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

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			t.Parallel()
			result, ok := nestedType.GetTypeFromPath(test.path)

			if test.shouldSucceed != ok {
				t.Errorf("GetTypeFromPath(%v) success = %v, want %v", test.path, ok, test.shouldSucceed)
				return
			}

			if !test.shouldSucceed {
				if result != nil {
					t.Errorf("GetTypeFromPath(%v) = %v, want nil", test.path, result)
				}
				return
			}

			if result.Kind != test.expectedKind {
				t.Errorf("GetTypeFromPath(%v) kind = %v, want %v", test.path, result.Kind, test.expectedKind)
			}

			if test.expectedKind == KindAtomic && result.AtomicType != test.expectedType {
				t.Errorf("GetTypeFromPath(%v) atomic type = %v, want %v", test.path, result.AtomicType, test.expectedType)
			}
		})
	}
}

func TestIsMorePrecise(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		type1    RegoTypeDef
		type2    RegoTypeDef
		expected bool
	}{
		{
			name:     "unknown is not more precise than atomic",
			type1:    NewUnknownType(),
			type2:    NewAtomicType(AtomicString),
			expected: false,
		},
		{
			name:     "atomic is more precise than unknown",
			type1:    NewAtomicType(AtomicString),
			type2:    NewUnknownType(),
			expected: true,
		},
		{
			name:     "atomic is more precise than array",
			type1:    NewAtomicType(AtomicString),
			type2:    NewArrayType(NewAtomicType(AtomicString)),
			expected: true,
		},
		{
			name:     "atomic types have equal precision",
			type1:    NewAtomicType(AtomicString),
			type2:    NewAtomicType(AtomicInt),
			expected: false,
		},
		{
			name:     "array with more precise element type",
			type1:    NewArrayType(NewAtomicType(AtomicString)),
			type2:    NewArrayType(NewUnknownType()),
			expected: true,
		},
		{
			name:     "array with equal element type precision",
			type1:    NewArrayType(NewAtomicType(AtomicString)),
			type2:    NewArrayType(NewAtomicType(AtomicString)),
			expected: false,
		},
		{
			name: "object with more fields is more precise",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
			}),
			expected: true,
		},
		{
			name: "object with same fields has equal precision",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
			}),
			expected: false,
		},
		{
			name: "nested object precision comparison",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewObjectType(map[string]RegoTypeDef{
					"nested1": NewAtomicType(AtomicInt),
					"nested2": NewAtomicType(AtomicBoolean),
				}),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewObjectType(map[string]RegoTypeDef{
					"nested1": NewAtomicType(AtomicInt),
				}),
			}),
			expected: true,
		},
		{
			name: "different field names don't affect precision",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field3": NewAtomicType(AtomicInt),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			expected: false,
		},
		{
			name: "object with less precise nested type is not more precise",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewUnknownType(),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			expected: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			result := tt.type1.IsMorePrecise(&tt.type2)
			if result != tt.expected {
				t.Errorf("IsMorePrecise() = %v, want %v", result, tt.expected)
			}
		})
	}
}

func TestIsEqual(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		type1    RegoTypeDef
		type2    RegoTypeDef
		expected bool
	}{
		{
			name:     "identical atomic types",
			type1:    NewAtomicType(AtomicString),
			type2:    NewAtomicType(AtomicString),
			expected: true,
		},
		{
			name:     "different atomic types",
			type1:    NewAtomicType(AtomicString),
			type2:    NewAtomicType(AtomicInt),
			expected: false,
		},
		{
			name:     "identical array types",
			type1:    NewArrayType(NewAtomicType(AtomicString)),
			type2:    NewArrayType(NewAtomicType(AtomicString)),
			expected: true,
		},
		{
			name:     "different array element types",
			type1:    NewArrayType(NewAtomicType(AtomicString)),
			type2:    NewArrayType(NewAtomicType(AtomicInt)),
			expected: false,
		},
		{
			name: "identical object types",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			expected: true,
		},
		{
			name: "objects with different field types",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicString),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			expected: false,
		},
		{
			name: "objects with different field names",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field2": NewAtomicType(AtomicInt),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"field3": NewAtomicType(AtomicInt),
			}),
			expected: false,
		},
		{
			name: "nested objects equal",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"nested": NewObjectType(map[string]RegoTypeDef{
					"inner": NewAtomicType(AtomicInt),
				}),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"nested": NewObjectType(map[string]RegoTypeDef{
					"inner": NewAtomicType(AtomicInt),
				}),
			}),
			expected: true,
		},
		{
			name: "nested objects different",
			type1: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"nested": NewObjectType(map[string]RegoTypeDef{
					"inner": NewAtomicType(AtomicInt),
				}),
			}),
			type2: NewObjectType(map[string]RegoTypeDef{
				"field1": NewAtomicType(AtomicString),
				"nested": NewObjectType(map[string]RegoTypeDef{
					"inner": NewAtomicType(AtomicString),
				}),
			}),
			expected: false,
		},
		{
			name:     "unknown types are equal",
			type1:    NewUnknownType(),
			type2:    NewUnknownType(),
			expected: true,
		},
		{
			name:     "unknown and atomic types are not equal",
			type1:    NewUnknownType(),
			type2:    NewAtomicType(AtomicString),
			expected: false,
		},
		{
			name:     "null array types are equal",
			type1:    RegoTypeDef{Kind: KindArray, ArrayType: nil},
			type2:    RegoTypeDef{Kind: KindArray, ArrayType: nil},
			expected: true,
		},
		{
			name:     "null and non-null array types are not equal",
			type1:    RegoTypeDef{Kind: KindArray, ArrayType: nil},
			type2:    NewArrayType(NewAtomicType(AtomicString)),
			expected: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			result := tt.type1.IsEqual(&tt.type2)
			if result != tt.expected {
				t.Errorf("IsEqual() = %v, want %v", result, tt.expected)
			}
			// Test symmetry
			result = tt.type2.IsEqual(&tt.type1)
			if result != tt.expected {
				t.Errorf("IsEqual() symmetry check: type2.IsEqual(type1) = %v, want %v", result, tt.expected)
			}
		})
	}
}
