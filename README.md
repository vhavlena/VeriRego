
# VeriRego 

![Go Test](https://github.com/vhavlena/VeriRego/actions/workflows/go-test.yml/badge.svg)

**VerRego** is a tool for formal verification of [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/) policies using SMT (Satisfiability Modulo Theories) solving and symbolic execution. It aims to provide confidence in policy correctness by automatically checking properties, detecting inconsistencies, and finding potential policy violations before deployment.

## Prerequisites

Some tests and functionality use the Z3 SMT solver via the Go bindings `github.com/vhavlena/z3-go`. You need Z3 installed on your system for those parts to build and run.

- macOS (Homebrew):
  - `brew install z3`
- Ubuntu/Debian (APT):
  - `sudo apt-get update && sudo apt-get install -y z3 libz3-dev`
- Windows:
  - Install the prebuilt Z3 binaries from https://github.com/Z3Prover/z3/releases and ensure `z3.dll` and headers are available on your PATH/Library path.

Notes:
- If your Z3 installation is in a non-standard location and you see linker errors (e.g., "library not found for -lz3"), you can point CGO to Z3, for example:
  - macOS (example): `export CGO_LDFLAGS="-L/opt/homebrew/lib"` and `export CGO_CFLAGS="-I/opt/homebrew/include"`
  - Linux (example): `export CGO_LDFLAGS="-L/usr/local/lib"` and `export CGO_CFLAGS="-I/usr/local/include"`
- Our CI installs Z3 automatically on Ubuntu; see the workflow in `.github/workflows/go-test.yml`.

## Type Inference Tool

The repository includes a type inference binary, `type_analysis`, which analyzes Rego policy files and infers types for all rules and variables. This tool helps you understand the structure and expected data types within your policies.

### Usage

```
./build/type_analysis -rego <policy.rego> [-yaml <input.yaml>] [-spec <spec.yaml>] [-inline] [-rego-version <0|1>]
```

- `-rego` (required): Path to the Rego policy file to analyze.
- `-yaml` (optional): Path to a YAML file providing input data for schema inference.
- `-spec` (optional): Path to a parameter specification file.
- `-rego-version` (optional): Rego language version to parse the policy with (`0` for Rego 0.x, `1` for Rego 1.x; default `1`).
- `-inline` (optional): If specified, enables inlining of rules and variables during type analysis. This can improve precision by replacing references with their definitions where possible.

The tool will output the inferred types for all rules in the provided policy.

## SMT Translation Tool

The repository includes an SMT translation binary, `smt`, which translates Rego policy files into SMT-LIB constraints for formal verification. This tool enables you to check the logical consistency of your policies and perform automated reasoning using SMT solvers.

### Usage

```
./build/smt -rego <policy.rego> [-yaml <input.yaml>] [-spec <spec.yaml>] [-out <output.smt2>] [-rego-version <0|1>]
```

- `-rego` (required): Path to the Rego policy file to translate.
- `-yaml` (optional): Path to a YAML file providing input data for schema inference.
- `-spec` (optional): Path to a parameter specification file.
- `-out` (optional): Path to the output SMT-LIB file (default: `out.smt2`).
- `-rego-version` (optional): Rego language version to parse the policy with (`0` for Rego 0.x, `1` for Rego 1.x; default `1`).

The tool outputs the SMT-LIB representation of the policy, including:
- **Type declarations and constraints** for all variables, objects, and arrays.
- **Translation of all Rego rules** to SMT-LIB assertions, where each rule is represented as a single assertion of the form:

  ```smtlib
  (assert (<=> (= ruleVar ruleValue) (and expr1 expr2 ... exprN)))
  ```

- **Translation of expressions** such as equality, arithmetic, and string operations to their SMT-LIB equivalents.

For a detailed description of the translation process and examples, see [`pkg/smt/rego_to_smt.md`](pkg/smt/rego_to_smt.md).

### Useful Links 
- Language specification: https://www.openpolicyagent.org/docs/policy-language
- Policy library: https://github.com/weaveworks/policy-library 
- Red Hat policies: https://github.com/redhat-cop/rego-policies/blob/main/POLICIES.md
- https://pkg.go.dev/github.com/open-policy-agent/opa@v1.4.2/v1
- https://github.com/open-policy-agent/example-api-authz-go
- Linter: https://www.openpolicyagent.org/ecosystem/entry/regal https://docs.styra.com/regal#try-it-out
- Redundant definition issue https://github.com/StyraInc/regal/issues/1523
- Policy example https://github.com/permitio/opal-example-policy-repo
- Cedar (AWS) https://github.com/cedar-policy