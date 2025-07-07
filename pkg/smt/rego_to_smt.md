# Rego Types to SMT-LIB Translation

This document summarizes how Rego types are translated into SMT-LIB datatypes and constraints, as implemented in the `pkg/smt/type_defs.go` file.

## Supported Rego Types
- **Atomic types**: string, int, boolean, null
- **Object types**: maps with string keys and typed values
- **Array types**: arrays with homogeneous element types

## SMT-LIB Datatype Declarations
The following SMT-LIB datatypes are used to represent Rego types:

```smtlib
(declare-datatypes ()
  ((OAtom
    (OString (str String))
    (ONumber (num Int))
    (OBoolean (bool Bool))
    ONull
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
  ((OGenTypeAtom (Atom (atom OAtom)) ))
)
```

## Type Sorts
Type sorts are defined recursively to support nested types:

```smtlib
(define-sort OTypeD0 () (OGenType OGenTypeAtom))
(define-sort OTypeD1 () (OGenType OTypeD0))
(define-sort OTypeD2 () (OGenType OTypeD1))
; ... up to the required depth
```

## Variable Declaration Example
A variable `x` of type depth 1:

```smtlib
(define-fun x () OTypeD1)
```

## Type Constraint Functions
- `is-Atom` for atomic types
- `is-OObj` for objects
- `is-OArray` for arrays

## Constraint Generation
### Atomic Types
For a variable `x` of atomic type:
```smtlib
(assert (is-OString (atom x)))
(assert (is-ONumber (atom x)))
(assert (is-OBoolean (atom x)))
```

### Object Types
For an object variable `objVar` with fields `foo` (string) and `bar` (int):
```smtlib
(assert (and
  (is-OObj objVar)
  (is-OString (atom (select (obj objVar) "foo")))
  (is-ONumber (atom (select (obj objVar) "bar")))
))
```

### Array Types
For an array variable `arrVar` of strings:
```smtlib
(assert (and
  (is-OArray arrVar)
  (forall ((i Int))
    (let ((elem (select (arr arrVar) i)))
      (is-OString (atom elem))
    )
  )
))
```

## Object Initialization Examples

Objects are initialized in SMT-LIB using the `OObj` constructor and the SMT array, following the approach used in the `getSmtObjectConstr` function. Each field is inserted using the `store` operation, and constraints are generated recursively for each field.

#### Example: Initializing an object with nested fields
Suppose you have a Rego object type:

```rego
{
  "foo": string,
  "bar": { "baz": int }
}
```

Constraints for each field are generated recursively, as in `getSmtObjectConstr`:

```smtlib
(assert (and
  (is-OObj myObj)
  (is-OString (atom (select (obj myObj) "foo")))
  (is-OObj (select (obj myObj) "bar"))
  (is-ONumber (atom (select (obj (select (obj myObj) "bar")) "baz")))
))
```

### Accessing Object Fields
To access a field, use:
```smtlib
(select (obj myObj) "foo") ; returns (Atom (OString "abc"))
```

### Example: Asserting Field Value
```smtlib
(assert (= (select (obj myObj) "foo") (Atom (OString "abc"))))
```

## Error Handling
If a type is not supported, an error is returned.

## Summary Table
| Rego Type         | SMT-LIB Representation         |
|-------------------|-------------------------------|
| string            | (OString (str String))         |
| int               | (ONumber (num Int))            |
| boolean           | (OBoolean (bool Bool))         |
| null              | ONull                          |
| object            | (OObj (obj (Array String T)))  |
| array             | (OArray (arr (Array Int T)))   |

---

For more details, see the implementation in `pkg/smt/type_defs.go`.
