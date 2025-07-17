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

## Expression and Rule Translation

### Expression Translation
Rego expressions are translated to SMT-LIB using the following principles:
- **Atomic expressions** (e.g., `x == 1`, `foo > 0`) are mapped to their SMT-LIB equivalents using the corresponding operator and arguments.
- **Supported operators** include arithmetic (`plus`, `minus`, `mul`, `div`), comparison (`eq`, `neq`, `gt`, `lt`, `equal`), and string operations (`concat`, `contains`, `startswith`, `endswith`, etc.).
- The translation is performed by converting the operator and its arguments to SMT-LIB syntax, e.g.:

```rego
x == 1
```
translates to:
```smtlib
(= x 1)
```

```rego
x != 2
```
translates to:
```smtlib
(not (= x 2))
```

```rego
plus(x, 1)
```
translates to:
```smtlib
(+ x 1)
```

### Rule Translation
Each Rego rule is translated to a single SMT-LIB assertion. The rule variable is equal to the rule value if and only if all body expressions are satisfied. The general form is:

```rego
p = x {
  x == 1
  x > 0
}
```
translates to:
```smtlib
(assert (= (= p x) (and (= x 1) (> x 0))))
```

If the rule has no body, the assertion is:
```rego
q = 42 {}
```
translates to:
```smtlib
(assert (= (= q 42) true))
```

#### Notes
- The translation supports rules with head keys and references (e.g., `violation[result] { ... }`), which are mapped to equality or, in the future, to set membership.
- All body expressions are combined using `and` in SMT-LIB.
- The translation is implemented in `pkg/smt/exprs.go` and `pkg/smt/rules.go`.

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
