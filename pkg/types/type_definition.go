// Package types provides type analysis for Rego AST.
package types

import (
	"github.com/open-policy-agent/opa/v1/ast"
)

// TypeKind represents the kind of a Rego type
type TypeKind string

const (
	KindAtomic  TypeKind = "atomic"
	KindArray   TypeKind = "array"
	KindObject  TypeKind = "object"
	KindUnknown TypeKind = "unknown"
	KindUnion   TypeKind = "union"
)

// AtomicType represents atomic types in Rego
type AtomicType string

const (
	AtomicString   AtomicType = "string"
	AtomicInt      AtomicType = "int"
	AtomicBoolean  AtomicType = "boolean"
	AtomicFunction AtomicType = "function"
	AtomicSet      AtomicType = "set"
	AtomicNull     AtomicType = "null"
	AtomicUndef    AtomicType = "undefined"
)

// RegoTypeDef represents a full type definition in Rego
type RegoTypeDef struct {
	Kind         TypeKind       // The kind of type (atomic, array, object)
	AtomicType   AtomicType     // The specific atomic type if Kind is atomic
	ArrayType    *RegoTypeDef   // The type of array elements if Kind is array
	ObjectFields ObjectFieldSet // The field types if Kind is object
	Union        []RegoTypeDef  // If KindUnion, this holds union member types
}

//----------------------------------------------------------------

// AdditionalPropertiesKey identifies the synthetic entry used to store
// additionalProperties types for object definitions.
const AdditionalPropKey = "*"

// ObjectFieldSet describes the fields of a Rego object type together with
// information about whether JSON Schema additionalProperties are permitted.
type ObjectFieldSet struct {
	Fields          map[string]RegoTypeDef
	AllowAdditional bool
}

func NewObjectFieldSet(fields map[string]RegoTypeDef, allowAdditional bool) ObjectFieldSet {
	return ObjectFieldSet{
		Fields:          fields,
		AllowAdditional: allowAdditional,
	}
}

// Get returns the type definition for the named field and a boolean
// indicating whether the field type was found.
//
// If the field is not present and AllowAdditional is true, the method will
// attempt to return the type stored under the synthetic key
// `AdditionalPropKey` (used to represent JSON Schema additionalProperties).
// The returned pointer points to a copy of the stored value. The boolean is
// true when a type was found and false otherwise.
func (of *ObjectFieldSet) Get(field string) (*RegoTypeDef, bool) {
	t, ok := of.Fields[field]
	if !ok && of.AllowAdditional {
		t, ok = of.Fields[AdditionalPropKey]
		return &t, ok
	}
	return &t, ok
}

// GetValues returns a slice containing copies of all field type definitions
// stored in the ObjectFieldSet. The iteration order is the map iteration
// order and therefore unspecified. If a synthetic entry exists for
// additional properties (keyed by `AdditionalPropKey`), it will be included
// in the returned slice like any other map entry.
func (of *ObjectFieldSet) GetValues() []RegoTypeDef {
	values := make([]RegoTypeDef, 0, len(of.Fields))
	for _, v := range of.Fields {
		values = append(values, v)
	}
	return values
}

// GetKeys returns a slice of all explicit object field names.
//
// The special synthetic key used for additionalProperties ("*",
// stored under `AdditionalPropKey`) is never included in the
// result, so the returned slice only contains concrete field names
// that may appear in Rego objects.
func (of *ObjectFieldSet) GetKeys() []string {
	keys := make([]string, 0, len(of.Fields))
	for k := range of.Fields {
		if k == AdditionalPropKey {
			continue
		}
		keys = append(keys, k)
	}
	return keys
}

// HasSetAdditionalProperties reports whether this ObjectFieldSet allows
// additional properties and has an explicit type stored for them.
//
// It returns true only when `AllowAdditional` is true and the
// synthetic field keyed by `AdditionalPropKey` is present in
// `Fields`, indicating that JSON Schema additionalProperties are
// permitted and typed.
func (of *ObjectFieldSet) HasSetAdditionalProperties() bool {
	_, has := of.Fields[AdditionalPropKey]
	return of.AllowAdditional && has
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
		ObjectFields: NewObjectFieldSet(fields, true),
	}
}

// NewUnionType creates a new RegoTypeDef for a union type
func NewUnionType(types []RegoTypeDef) RegoTypeDef {
	return RegoTypeDef{
		Kind:  KindUnion,
		Union: types,
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

// IsUnion returns true if the type is a union
func (t *RegoTypeDef) IsUnion() bool {
	return t.Kind == KindUnion
}

// MakeUnion ensures the receiver is a union type and returns a pointer to it.
//
// If the receiver is already a union this method simply returns the receiver.
// Otherwise, it mutates the receiver in-place by changing its Kind to
// KindUnion and wrapping the previous value as the single member of the
// resulting union. The returned pointer references the (possibly modified)
// receiver.
//
// Side effects: the receiver's Kind and Union fields may be mutated.
func (t *RegoTypeDef) MakeUnion() *RegoTypeDef {
	if t.IsUnion() {
		return t
	}
	t.Kind = KindUnion
	t.Union = []RegoTypeDef{*t}
	return t
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
	fieldType, exists := t.ObjectFields.Get(field)
	if !exists {
		return nil, false
	}
	return fieldType, true
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
		if len(t.ObjectFields.Fields) != len(other.ObjectFields.Fields) {
			return false
		}
		if t.ObjectFields.AllowAdditional != other.ObjectFields.AllowAdditional {
			return false
		}
		for field, type1 := range t.ObjectFields.Fields {
			type2, exists := other.ObjectFields.Fields[field]
			if !exists || !type1.IsEqual(&type2) {
				return false
			}
		}
		return true
	case KindUnion:
		if len(t.Union) != len(other.Union) {
			return false
		}
		return t.subsetUnion(other.Union) && other.subsetUnion(t.Union)
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
	if len(t.ObjectFields.Fields) < len(other.ObjectFields.Fields) {
		return false
	}
	if other.ObjectFields.AllowAdditional != t.ObjectFields.AllowAdditional {
		return false
	}

	// Check common fields recursively
	for fieldName, otherType := range other.ObjectFields.Fields {
		thisType, exists := t.ObjectFields.Fields[fieldName]
		if !exists {
			return false
		}
		// For common fields, this type should be at least as precise
		if !thisType.IsMorePrecise(&otherType) && !thisType.IsEqual(&otherType) {
			return false
		}
	}

	// Must have strictly more fields or equal fields with at least one being more precise
	return len(t.ObjectFields.Fields) > len(other.ObjectFields.Fields) || hasMorePreciseField(t, other)
}

// hasMorePreciseField checks if any field in t1 is more precise than the corresponding field in t2
func hasMorePreciseField(t1, t2 *RegoTypeDef) bool {
	for fieldName, type1 := range t1.ObjectFields.Fields {
		type2, exists := t2.ObjectFields.Fields[fieldName]
		if !exists {
			continue
		}
		if type1.IsMorePrecise(&type2) {
			return true
		}
	}
	return false
}

// IsMorePrecise reports whether t is strictly more precise than other.
//
// Precision rules (summary):
//   - Unknown is the least precise type. If t is unknown, it is not more precise
//     than any type. If other is unknown and t is not, t is considered more precise.
//   - If kinds differ (except for unknown), types are incomparable and neither is
//     more precise than the other.
//   - For arrays, precision is determined by the element type: an array is more
//     precise if its element type is more precise than the other's element type.
//   - For objects, a type is more precise if it has at least the same fields as
//     the other and each corresponding field type is at least as precise, and
//     either it has strictly more fields or at least one corresponding field is
//     strictly more precise (see compareObjects and hasMorePreciseField).
//   - For unions, the receiver delegates to isMorePreciseUnion: a union is more
//     precise than another union when every member of the receiver is present in
//     the other (subset relation).
//
// Returns true when t can be considered strictly more precise than other.
func (t *RegoTypeDef) IsMorePrecise(other *RegoTypeDef) bool {
	if t.IsUnknown() {
		return false
	}
	if other.IsUnknown() {
		return true
	}
	if t.IsUnion() {
		return t.isMorePreciseUnion(other)
	}
	if t.Kind != other.Kind {
		return false // Different kinds are incomparable
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
	case KindUnion:
		panic("unreachable")
	}
	return false
}

// subsetUnion reports whether the receiver (which must be a union type)
// is a subset of the provided slice of union members. It returns true when
// every member of the receiver's union has an equal member in `other`.
// The method panics if called on a non-union receiver.
func (t *RegoTypeDef) subsetUnion(other []RegoTypeDef) bool {
	if !t.IsUnion() {
		panic("subsetUnion called on non-union type")
	}

	for _, u := range t.Union {
		found := false
		for _, o := range other {
			if u.IsEqual(&o) {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}

// isMorePreciseUnion compares two union types for precision. The receiver
// must be a union; the function returns true when every member of the
// receiver's union appears (by equality) in `other`'s union. If `other`
// is not a union the function returns false. It panics if called on a
// non-union receiver.
func (t *RegoTypeDef) isMorePreciseUnion(other *RegoTypeDef) bool {
	if !t.IsUnion() {
		panic("isMorePreciseUnion called on non-union type")
	}
	if !other.IsUnion() {
		return false
	}
	return t.subsetUnion(other.Union)
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
//   - For union types, GetTypeFromPath is applied to each member and a union of all
//     successful results is returned. If no members resolve successfully, returns (nil, false).
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
		// for non-ground keys (= variables), we take union of all field types.
		if !path[0].IsGround {
			if len(t.ObjectFields.Fields) == 0 {
				return nil, false
			}
			unionType := NewUnionType(t.ObjectFields.GetValues())
			unionType.CanonizeUnion()
			return unionType.GetTypeFromPath(remainingPath)
		}

		fieldType, exists := t.ObjectFields.Get(currentKey)
		if !exists {
			return nil, false
		}
		if len(remainingPath) == 0 {
			return fieldType, true
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
	case KindUnion:
		// Apply GetTypeFromPath to each union member and collect results
		var results []RegoTypeDef
		for i := range t.Union {
			if result, ok := t.Union[i].GetTypeFromPath(path); ok && result != nil {
				results = append(results, *result)
			} else {
				results = append(results, NewAtomicType(AtomicUndef))
			}
		}
		if len(results) == 0 {
			return nil, false
		}
		// Return union of all results
		unionResult := NewUnionType(results)
		unionResult.CanonizeUnion()
		return &unionResult, true
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
		if len(t.ObjectFields.Fields) == 0 {
			return "object{}"
		}
		result := "object{\n"
		for k, v := range t.ObjectFields.Fields {
			result += ind + spaces + k + ": " + v.prettyPrintWithIndentShort(indent+1, short) + "\n"
		}
		result += ind + "}"
		return result
	case KindUnion:
		if short {
			return "union"
		}
		if len(t.Union) == 0 {
			return "union{}"
		}
		result := "union[\n"
		for _, m := range t.Union {
			result += ind + spaces + m.prettyPrintWithIndentShort(indent+1, short) + "\n"
		}
		result += ind + "]"
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
		for _, fieldType := range t.ObjectFields.Fields {
			depth := fieldType.TypeDepth()
			if depth > maxDepth {
				maxDepth = depth
			}
		}
		return 1 + maxDepth
	case KindUnion:
		maxDepth := 0
		for _, memberType := range t.Union {
			depth := memberType.TypeDepth()
			if depth > maxDepth {
				maxDepth = depth
			}
		}
		return maxDepth
	}
	return 0
}

// flattenUnion recursively flattens nested union types.
// If the receiver is a union containing other unions as members, this method
// will recursively extract all non-union members into a single flat union.
// This is a no-op when the receiver is not a union.
//
// Example:
//
//	union[int, union[string, boolean]] becomes union[int, string, boolean]
func (t *RegoTypeDef) flattenUnion() {
	if !t.IsUnion() {
		return
	}

	flattened := make([]RegoTypeDef, 0, len(t.Union))
	for i := range t.Union {
		member := t.Union[i]
		if member.IsUnion() {
			// Recursively flatten nested unions
			member.flattenUnion()
			// Add all members of the nested union
			flattened = append(flattened, member.Union...)
		} else {
			// Add non-union member directly
			flattened = append(flattened, member)
		}
	}
	t.Union = flattened
}

// CanonizeUnion canonicalizes a union type in-place.
//
// Behavior:
//   - If the receiver is not a union, the method is a no-op.
//   - Nested union members are first flattened so the union is single-level.
//   - Duplicate members (by deep equality) are removed while preserving the
//     first-occurrence order of unique members.
//   - If, after deduplication, the union contains more than one member,
//     any unknown types are removed (unknown is treated as least precise).
//   - If the union reduces to a single member, the receiver is replaced by
//     that member (i.e., single-member unions are simplified).
//
// Side effects: mutates the receiver (`t.Union`) and may change the receiver's
// kind when simplifying single-member unions.
func (t *RegoTypeDef) CanonizeUnion() {
	if !t.IsUnion() {
		return
	}

	t.flattenUnion()
	unique := make([]RegoTypeDef, 0, len(t.Union))
	nonUnknown := make([]RegoTypeDef, 0, len(t.Union))
	for i := range t.Union {
		item := t.Union[i]
		found := false
		for j := range unique {
			if unique[j].IsEqual(&item) {
				found = true
				break
			}
		}
		if !found {
			unique = append(unique, item)
		}
	}

	// if len(unique) > 1, remove all unknown types
	if len(unique) > 1 {
		for i := range unique {
			if !unique[i].IsUnknown() {
				nonUnknown = append(nonUnknown, unique[i])
			}
		}
		unique = nonUnknown
	}

	t.Union = unique
	if len(t.Union) == 1 {
		// Simplify single-member union to that member type
		*t = t.Union[0]
	}
}
