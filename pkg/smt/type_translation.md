# Rego Types to SMT Type Encoding

This document describes how internal Rego types (`types.RegoTypeDef`) are mapped to SMT-LIB datatypes and constraints, as implemented in `pkg/smt/type_translator.go`.

Scope: only the *type layer* (value shapes and type guards). Expression/rule translation lives elsewhere (see `pkg/smt/rego_to_smt.md`).

## Overview: depth-indexed value datatypes

The current implementation uses a **depth-indexed family of datatypes** named `OTypeD0`, `OTypeD1`, ..., where depth is derived from `RegoTypeDef.TypeDepth()`.

- `OTypeD0` represents **atomic values only**.
- `OTypeD(d>0)` represents a **value** that can be atomic, object, or array, where nested values are stored one depth lower (`OTypeD(d-1)`).

This is the “simplified scheme” referenced in `getDatatypesDeclaration`.

### Datatype declarations (generated)

The translator always emits `OTypeD0` plus `OTypeD1..OTypeD(maxDepth)` (inclusive), where `maxDepth` is the maximum `TypeDepth()` among the variables selected by `GenerateTypeDecls`.

Shape (schematic):

```smtlib
(declare-datatypes ()
  ((OTypeD0
    (OString (str String))
    (ONumber (num Int))
    (OBoolean (bool Bool))
    ONull
    OUndef
  ))
)

; for each d = 1..maxDepth:
(declare-datatypes ()
  ((OTypeD<d>
    (Atom<d>   (atom<d>   OTypeD<d-1>))
    (OObj<d>   (obj<d>    (Array String OTypeD<d-1>)))
    (OArray<d> (arr<d>    (Array Int    OTypeD<d-1>)))
  ))
)
```

Notes:

- Atomic constructors at `OTypeD0` are `OString`, `ONumber`, `OBoolean`, `ONull`, `OUndef`.
- For `d>0`, the atomic case is represented via `Atom<d>` whose payload is an `OTypeD(d-1)` value.

## Mapping Rego types to SMT sorts

The SMT sort chosen for a `RegoTypeDef tp` is:

```text
OTypeD(tp.TypeDepth())
```

This is implemented by `getSmtType`.

Important consequence: **atomic types do not necessarily use `OTypeD0` for variables**. Variables are declared using `OTypeD(depth)` even for atomic `tp`, so atoms can be “embedded” at the right depth when needed by the overall model.

## Type predicates (guards)

The translator uses constructor testers to guard the shape of values.

### Atomic predicates

For atomic `tp`, the predicate name is one of:

- `is-OString`
- `is-ONumber`
- `is-OBoolean`
- `is-ONull`
- `is-OUndef`

This is implemented by `getTypeConstr` for `tp.IsAtomic()`.

### Object/array predicates

For non-atomic types, predicates are **depth-indexed**:

- Object: `is-OObj<d>`
- Array: `is-OArray<d>`

where `d = max(tp.TypeDepth(), 0)` for the current value.

## Constraint generation by type kind

The main entry is `getSmtConstr(smtValue, tp)`; `getSmtConstrAssert` wraps the result into `(assert (and ...))`.

### Atomic types

For atomic values, the constraint is a single predicate application:

```smtlib
(is-OString x)
(is-ONumber x)
(is-OBoolean x)
(is-ONull x)
(is-OUndef x)
```

This is produced by `getSmtAtomConstr`.

Atomic *values* used in expressions are wrapped using `getSmtValue` / `getAtomValue`:

- At depth 0:
  - string: `(str <expr>)`
  - int: `(num <expr>)`
  - bool: `(bool <expr>)`
- At depth $d>0$ (embedding into `OTypeD<d>`):
  - string: `(str (atom<d> <expr>))`
  - int: `(num (atom<d> <expr>))`
  - bool: `(bool (atom<d> <expr>))`

`null` and `undefined` are represented as `ONull` / `OUndef`.

### Object types

For an object value `o` with depth `d = tp.TypeDepth()`, the translator emits:

1) A shape guard:

```smtlib
(is-OObj<d> o)
```

2) Per-field constraints for each explicit field key `$k$` (keys are sorted for determinism):

```smtlib
(let ((sel (select (obj<d> o) "k"))) ...)
```

In practice the selection is inlined:

```smtlib
(select (obj<d> o) "k")
```

- If the field type is non-atomic, an additional depth-indexed predicate is added for the selected value using `getTypeConstr(d-1, fieldType)`.
- Then `getSmtConstr` recurses into the selected value for full structural constraints.

3) `additionalProperties` constraints

Object additional-properties behavior is driven by `types.ObjectFieldSet`:

- `AllowAdditional == false`: additional keys are **disallowed**.
- `AllowAdditional == true` and a synthetic entry exists under key `types.AdditionalPropKey` (`"*"`): additional keys are **allowed and typed**.
- `AllowAdditional == true` with no `"*"` entry: additional keys are **allowed and unconstrained** (no universal constraint emitted).

When additional keys are disallowed *or* an additional-property type is set, `getSmtObjectConstr` emits a universal constraint over all `String` keys:

```smtlib
(forall ((k String))
  (or
    (= k "f1")
    ...
    (= k "fn")
    <default-condition>
  )
)
```

The `<default-condition>` is:

- If additional keys are disallowed:
  - `(is-OUndef (select (obj<d> o) k))`
- If additional keys are allowed and typed with type `T_add`:
  - `(<pred-for-T_add> (select (obj<d> o) k)) (is-OUndef (select (obj<d> o) k))`
  - Note: the current implementation places **both** conjuncts directly into the `or` list, effectively allowing either the additional-type predicate or `OUndef`.

The quantified key name is generated via `RandString(5)`.

### Array types

For an array value `a` with depth `d = tp.TypeDepth()`, the translator emits:

1) A shape guard:

```smtlib
(is-OArray<d> a)
```

2) A universal constraint over all integer indices enforcing the element type:

```smtlib
(forall ((i Int))
  (let ((elem (select (arr<d> a) i)))
    (and <constraints-for-elem>)
  )
)
```

The element constraints are generated by recursing with `getSmtConstr("elem", tp.ArrayType)`.

### Union types

Union types (`tp.IsUnion()`) are encoded as a single disjunction. For each union member, its constraints are computed for the **same** `smtValue` and concatenated inside one big `(or ...)`:

```smtlib
(or <member1-constraints...> <member2-constraints...> ...)
```

This is implemented in `getSmtUnionConstr`.

## Variable declarations

For each used variable name `x`, `GenerateVarDecl` emits:

```smtlib
(declare-fun x () OTypeD<tp.TypeDepth()>)
(assert (and <constraints-for-x>))
```

`GenerateTypeDecls` chooses the maximum depth across the selected variables and emits datatype declarations up to that depth.

## Limitations / non-supported types

`types.AtomicFunction` and `types.AtomicSet` are currently rejected in type constraints (`ErrUnsupportedAtomic`).

## Pointers into the implementation

- Sort selection: `TypeTranslator.getSmtType`
- Datatype generation: `TypeTranslator.getDatatypesDeclaration`
- Constraint generation entry: `TypeTranslator.getSmtConstr` / `TypeTranslator.getSmtConstrAssert`
- Object constraints: `TypeTranslator.getSmtObjectConstr`
- Array constraints: `TypeTranslator.getSmtArrConstr`
- Unions: `TypeTranslator.getSmtUnionConstr`
