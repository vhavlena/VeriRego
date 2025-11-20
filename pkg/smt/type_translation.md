# Rego Types to SMT Type Encoding

This document describes how internal Rego types (`RegoTypeDef`) are mapped to SMT-LIB sorts and constraints, as implemented in `pkg/smt/type_translator.go` and used by the SMT translation tool.

It focuses on the *type layer* only: how values and shapes are encoded, not on how individual Rego expressions and rules are translated.

## Overview

VeriRego uses a small algebra of generic SMT datatypes:

- `OAtom` – atomic values (string, integer/number, boolean, null, undefined)
- `OGenType T` – generic container for:
  - `Atom OAtom`
  - `OObj (Array String T)` – objects as maps from string keys to values of type `T`
  - `OArray (Array Int T)` – arrays as maps from integer indices to values of type `T`
- `OGenTypeAtom` – specialization of `OGenType` where nested values are always `OAtom`.

For nested types, a family of *depth-indexed* sorts is defined:

- `OTypeD0  = OGenType OGenTypeAtom`
- `OTypeD1  = OGenType OTypeD0`
- `OTypeD2  = OGenType OTypeD1`
- … up to the maximum depth observed in the inferred type information.

The depth of a Rego type (`TypeDepth()`) is roughly:

- Atomic: depth 1
- Array/object: `1 + max(depth of element/field types)`

A Rego value of depth `d` is represented by the SMT sort `OTypeD(d-1)`.

## SMT Datatype Declarations

The generator always emits the following datatype declarations (see `getDatatypesDeclaration`):

```smtlib
(declare-datatypes ()
  ((OAtom
    (OString (str String))
    (ONumber (num Int))
    (OBoolean (bool Bool))
    ONull
    OUndef
  ))
)

(declare-datatypes (T)
  ((OGenType
    (Atom (atom OAtom))
    (OObj (obj (Array String T)))
    (OArray (arr (Array Int T)))
  ))
)

(declare-datatypes ()
  ((OGenTypeAtom (Atom (atom OAtom))))
)
```

Then, depending on the maximum type depth `maxDepth` among all used variables, it emits sort aliases (see `getSortDefinitions`):

```smtlib
(define-sort OTypeD0 () (OGenType OGenTypeAtom))
(define-sort OTypeD1 () (OGenType OTypeD0))
(define-sort OTypeD2 () (OGenType OTypeD1))
; ... up to OTypeD(maxDepth-1)
```

## Mapping Rego Types to SMT Sorts

Given a Rego type `tp` with `tp.TypeDepth() = d >= 1`, its SMT sort is:

```text
OTypeD(d-1)
```

This mapping is implemented in `getSmtType`.

Examples:

- Atomic type (`string`, `int`, `boolean`, `null`): `TypeDepth() = 1` → sort `OTypeD0`
- Array of atomic (`[string]`): `TypeDepth() = 2` → sort `OTypeD1`
- Object with nested object field: `TypeDepth() >= 3` → sort `OTypeD2` or deeper.

All declared variables use this mapping:

```smtlib
(declare-fun x () OTypeD1)
(declare-fun input_review_object () OTypeD2)
```

## Type Kind Predicates

A helper predicate name is chosen from a Rego type using `getTypeConstr(tp)`:

- Atomic → `is-Atom`
- Array  → `is-OArray`
- Object → `is-OObj`

These are used as *guards* to state that a value is of the expected variant of `OGenType`.

## Constraint Generation per Rego Type

For each variable or intermediate value, `getSmtConstr` generates a set of SMT constraints that enforce the shape implied by the Rego type.

The final assertion for a variable `v` is:

```smtlib
(assert (and <constraints for v>))
```

(See `getSmtConstrAssert`.)

### Atomic Types

Atomic types correspond to `Atom` values carrying a specific `OAtom` constructor:

- Rego `string`   → `(Atom (OString ...))`
- Rego `int`      → `(Atom (ONumber ...))`
- Rego `boolean`  → `(Atom (OBoolean ...))`
- Rego `null`     → `(Atom ONull)`

For an atomicly-typed value `x` (of some `OTypeDk`), constraints are of the form:

```smtlib
(is-Atom x)
; plus additional constraints when x is known to be specifically string/int/bool/null
```

(Details of the per-constructor tests are handled in the expression translation and are not repeated here.)

### Object Types

Rego objects are represented as `OObj` over an SMT array `(Array String T)`.

Given an object-typed value `o` and its type description with fields `f1, ..., fn`, `getSmtObjectConstr` generates:

1. A guard that `o` is an object when it contains non-atomic fields.
2. For each *declared* field `fi`:
   - A select over the underlying array:
     ```smtlib
     (select (obj o) "fi")
     ```
   - A kind guard when the field type is non-atomic:
     ```smtlib
     (is-OObj (select (obj o) "fi"))
     ; or is-OArray, etc.
     ```
   - Recursively generated constraints for the selected value (using `getSmtConstr`).

3. A universal constraint over *all* string keys, encoding `additionalProperties` semantics from the type layer:

   - If additional properties are **not allowed**:
     ```smtlib
     (forall ((k String))
       (or (= k "f1") ... (= k "fn")
           (= (select (obj o) k) (Atom OUndef)))
     )
     ```

   - If additional properties are allowed with a specific type `T_add`:
     ```smtlib
     (forall ((k String))
       (or (= k "f1") ... (= k "fn")
           ; value at k must satisfy constraints of T_add
           <constraints for (select (obj o) k) wrt T_add>)
     )
     ```

   - If additional properties are allowed and unconstrained, the universal quantifier is omitted and unlisted keys may map to any value.

The quantified key variable name is generated using `RandString` to avoid collisions.

### Array Types

Rego arrays are represented as `OArray` over an SMT array `(Array Int T)`.

For an array-typed value `a` with element type `E`, `getSmtArrConstr` (not fully shown here) generates:

1. A guard that `a` is an array (when necessary):
   ```smtlib
   (is-OArray a)
   ```

2. A universal constraint over integer indices, enforcing the element type:
   ```smtlib
   (forall ((i Int))
     <constraints for (select (arr a) i) wrt element type E>
   )
   ```

When `E` is an object type that itself has `additionalProperties`, those constraints are nested accordingly.

### Union Types

Rego union types (e.g. coming from JSON Schema `anyOf`/`oneOf` or internal merges) are encoded as a disjunction of member constraints.

Given `tp` where `tp.IsUnion()` holds and a value `v`:

```smtlib
(or
  <constraints for v wrt member_1>
  <constraints for v wrt member_2>
  ...
)
```

This is implemented by `getSmtUnionConstr`.

## Variable Declarations and Usage

For each Rego variable `x` whose type has been inferred, `GenerateVarDecl` produces:

- A declaration using `getSmtType`:
  ```smtlib
  (declare-fun x () OTypeDk)
  ```
- A matching assertion with all structural constraints:
  ```smtlib
  (assert (and <constraints for x>))
  ```

`GenerateTypeDecls` is responsible for emitting the shared datatype and sort declarations for **all** used variables, based on the maximum type depth.

## Summary

- All Rego values live in a small family of polymorphic SMT datatypes (`OAtom`, `OGenType`).
- The depth of a Rego type determines which `OTypeDk` sort is used.
- Objects and arrays are backed by SMT arrays and constrained via quantified formulas.
- JSON Schema–derived and analysis-derived types are treated uniformly at this layer – once they are expressed as `RegoTypeDef`, they follow the same SMT encoding.

For the translation of actual Rego *expressions* and *rules* on top of this encoding, see `pkg/smt/rego_to_smt.md` and the implementations in `pkg/smt/exprs.go` and `pkg/smt/rules.go`.
