# Input JSON Schema: Supported features

This describes the JSON Schema features that are understood when defining the shape of `input` using `InputJsonSchema`.

Focus: a practical list of supported keywords and what they mean. No internal implementation details.

The implementation is intentionally approximate: it maps JSON Schema into the internal `RegoTypeDef` type system that is later used by the type analyzer and SMT translator.

## Types ("type")

Supported basic JSON Schema types:
- `"object"`
- `"array"`
- `"string"`
- `"integer"` (also accepts `"number"` – both map to the same integer type)
- `"boolean"`
- `"null"`

You can also use an array of types, e.g. `["string", "null"]` to allow multiple kinds of values; this becomes an internal union type.

If `type` is omitted, the tool tries to infer the kind from `properties` / `items`. Otherwise the type is treated as unknown.

## Objects

Objects are created when `"type": "object"` is present, or when `properties` is used without an explicit `type`.

- `properties`
  - Defines named fields and their types.
  - Each property schema is recursively converted.
  - Example:
    ```json
    {
      "type": "object",
      "properties": {
        "name": {"type": "string"},
        "age":  {"type": "integer"}
      }
    }
    ```

- `additionalProperties`
  - Controls unknown / dynamic object keys.
  - Supported values:
    - `false` — extra fields are **not** allowed; any key other than `properties` keys is constrained to an internal `undefined` value.
    - `true` — extra fields are allowed; their type is approximated as **unknown** (no further constraints).
    - `{ ...schema... }` — extra fields are allowed and must follow the given schema; that schema is recursively converted, and is used for any unknown key.
  - Nested `additionalProperties` are supported (e.g. object-of-objects).
  - Example with typed `additionalProperties`:
    ```json
    {
      "type": "object",
      "properties": {"known": {"type": "boolean"}},
      "additionalProperties": {"type": "string"}
    }
    ```

- Non‑ground (variable) object keys
  - When a path uses a variable instead of a concrete property name, the resulting type is:
    - the union of all `properties` types, **or**
    - the `additionalProperties` type (if present), **or**
    - unknown (for `additionalProperties: true`).

## Arrays

Arrays are created when `"type": "array"` is present, or when `items` is used without an explicit `type`.

- `items` (single schema)
  - All elements follow that schema.
  - Internally, the array element type is the converted type of `items`.
  - Example:
    ```json
    {
      "type": "array",
      "items": {"type": "string"}
    }
    ```

- `items` (array of schemas – tuple style)
  - A JSON Schema tuple like `"items": [S1, S2, ...]` is approximated as **array of union(element types)**.
  - That is, any index is treated as having a type that is the union of all tuple element types.
  - Example:
    ```json
    {
      "type": "array",
      "items": [
        {"type": "string"},
        {"type": "integer"}
      ]
    }
    ```
    becomes an array whose element type is `string | integer`.

- Arrays of objects with `additionalProperties`
  - When `items` is an object schema that uses `additionalProperties`, unknown object keys inside each array element are handled the same way as for top‑level objects.

## Combining schemas

The following combinators are supported and converted into internal union / merge operations:

- `anyOf`, `oneOf`
  - The value may match any one of the listed schemas.
  - The result is the **union** of the member types.
  - Example:
    ```json
    {
      "anyOf": [
        {"type": "string"},
        {"type": "integer"}
      ]
    }
    ```

- `allOf`
  - Multiple schemas are combined conjunctively.
  - Object schemas: fields from all parts are merged (similar to intersection of field maps).
  - Array schemas: element constraints are merged when compatible.
  - Mixed / incompatible combinations fall back to an approximate union‑like merge.
  - Example:
    ```json
    {
      "allOf": [
        {"type": "object", "properties": {"a": {"type": "string"}}},
        {"type": "object", "properties": {"b": {"type": "integer"}}}
      ]
    }
    ```

- Combinators with `additionalProperties`
  - When `anyOf` / `oneOf` / `allOf` combine object schemas that have `additionalProperties`, the resulting additional‑property type is the (merged) combination of the branch types (e.g. a union of `string` and `integer`).

## Notes and current gaps

Currently **ignored or treated as unknown**:
- `$ref`
- `enum`, `const`
- `required`, `additionalItems`, `patternProperties`, `dependencies`, `if` / `then` / `else`
- Numeric or string constraints: `minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`, `minLength`, `maxLength`, `pattern`, `format`, etc.

Approximations:
- `"number"` is treated like `"integer"` (no separate float type).
- Tuples (`items` as an array) are approximated as arrays with a **single union element type**.

If a keyword is not listed above, it is currently ignored.
