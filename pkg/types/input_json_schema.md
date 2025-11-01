# Input JSON Schema: Supported features

This describes the JSON Schema features that are understood when defining the shape of `input`.

Focus: a practical list of supported keywords and what they mean. No internal details.

## Types ("type")

Supported basic types:
- object
- array
- string
- integer (also accepts number)
- boolean
- null

You can also use an array of types, e.g. `["string", "null"]` to allow multiple kinds of values.

## Objects

- properties: Defines named fields and their types.
  - Example:
    ```json
    {"type":"object","properties":{"name":{"type":"string"},"age":{"type":"integer"}}}
    ```

- additionalProperties:
  - false — extra fields are not allowed via this mechanism.
  - true — extra fields are allowed (their values are treated as unconstrained type-wise).
  - { ...schema... } — extra fields are allowed and must follow the given schema.
  - Example:
    ```json
    {"type":"object","properties":{"known":{"type":"boolean"}},"additionalProperties":{"type":"string"}}
    ```

## Arrays

- items:
  - Single schema — all elements follow that schema.
    - Example: `{ "type":"array", "items": {"type":"string"} }`
  - Array of schemas (tuple style) — elements may be any of the listed item types.
    - Example: `{ "type":"array", "items": [ {"type":"string"}, {"type":"integer"} ] }`

## Combining schemas

- anyOf, oneOf — value may match any one of the listed schemas (either/or).
  - Example: `{ "anyOf": [ {"type":"string"}, {"type":"integer"} ] }`

- allOf — combine multiple schemas:
  - For objects, fields from all parts are combined.
  - For arrays, element constraints are combined.
  - In mixed or incompatible cases, it’s treated loosely as allowing either side.
  - Example:
    ```json
    {"allOf":[
      {"type":"object","properties":{"a":{"type":"string"}}},
      {"type":"object","properties":{"b":{"type":"integer"}}}
    ]}
    ```

## Notes and current gaps

Not supported/ignored:
- $ref
- enum, const
- required, additionalItems, patternProperties, dependencies, if/then/else
- Numeric or string constraints (minimum, maximum, pattern, format, etc.)

Minor approximation:
- "number" is treated like "integer" (no separate float type).

If a keyword is not listed above, it’s currently ignored.
