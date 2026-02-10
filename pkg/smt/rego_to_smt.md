# Rego to SMT-LIB Translation

This document summarizes the current Rego → SMT-LIB translation pipeline as implemented in:

- `pkg/smt/translator.go` (orchestration)
- `pkg/smt/type_translator.go` (SMT datatypes + type constraints)
- `pkg/smt/exprs.go` (expression translation)
- `pkg/smt/rules.go` (rule translation)

The type encoding details are documented more precisely in `pkg/smt/type_translation.md`.

## High-level flow

`Translator.GenerateSmtContent()` produces SMT-LIB in this order:

1. Datatype declarations for `OTypeD0..OTypeD<maxDepth>`
2. Variable declarations for selected global variables
3. Rule assertions for all rules in the module

The final output is returned by `Translator.SmtLines()`.

## Type layer (overview)

The implementation uses a depth-indexed family of datatypes `OTypeD0`, `OTypeD1`, ...:

- `OTypeD0` represents atomic values (`OString`, `ONumber`, `OBoolean`, `ONull`, `OUndef`).
- For depth $d>0$, `OTypeD<d>` has constructors `Atom<d>`, `OObj<d>`, `OArray<d>`, and `Wrap<d>`.

Datatype declarations are emitted via `TypeTranslator.GenerateTypeDecls`.

Variables are declared via `TypeTranslator.GenerateVarDecls` using:

```smtlib
(declare-fun x () OTypeD<d>)
(assert (and <type-constraints-for-x>))
```

See `pkg/smt/type_translation.md` for the exact constructor shapes and constraints.

## Expression translation

Expressions are translated by `ExprTranslator.ExprToSmt` / `termToSmt`.

Supported term kinds (current behavior):

- String/number/bool literals → SMT literals
- Variables (`ast.Var`) → translated using type-aware access (`TypeTranslator.getVarValue`)
- Input references (`ast.Ref` starting with `input`) → translated to selects over the schema/parameter variables and then made type-consistent via `TypeTranslator.getSmtValue`
- Constant objects (`ast.Object`) → encoded using SMT arrays (`store` over `as const`) in `handleConstObject`
- Explicit arrays (`*ast.Array`) → converted into a fresh SMT variable + constraints in `explicitArrayToSmt`

Builtins/operators:

- Several builtins are mapped to native SMT operators in `regoFuncToSmt` (e.g. `plus`→`+`, `eq`→`=`, `contains`→`str.contains`, etc.).
- `neq` is encoded as `(not (= ...))`.
- Unknown functions are declared as uninterpreted functions (with a fresh name) and then applied.

Unsupported term kinds return an error (e.g. sets).

## Rule translation

Rules are translated by `Translator.RuleToSmt`.

For a rule with head `(= <ruleVar> <ruleValue>)` and body conditions combined into `<body>`, the translator emits:

```smtlib
(assert (= (= <ruleVar> <ruleValue>) <body>))
```

Where `<body>` is:

- `true` if the rule has no body
- a single SMT expression if the body has one expression
- `(and e1 e2 ... en)` if the body has multiple expressions

Notes:

- Rule head values are converted through the expression translator.
- Some head shapes (e.g. `violation[result]`) are currently handled in a simplified way (see comments in `pkg/smt/rules.go`).

