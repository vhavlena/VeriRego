# VeriRego

**VerRego** is a tool for formal verification of [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/) policies using SMT (Satisfiability Modulo Theories) solving and symbolic execution. It aims to provide confidence in policy correctness by automatically checking properties, detecting inconsistencies, and finding potential policy violations before deployment.

## Type Inference Tool

The repository includes a type inference binary, `type_analysis`, which analyzes Rego policy files and infers types for all rules and variables. This tool helps you understand the structure and expected data types within your policies.

### Usage

```
./build/type_analysis -rego <policy.rego> [-yaml <input.yaml>] [-spec <spec.yaml>] [-inline]
```

- `-rego` (required): Path to the Rego policy file to analyze.
- `-yaml` (optional): Path to a YAML file providing input data for schema inference.
- `-spec` (optional): Path to a parameter specification file.
- `-inline` (optional): If specified, enables inlining of rules and variables during type analysis. This can improve precision by replacing references with their definitions where possible.

The tool will output the inferred types for all rules in the provided policy.