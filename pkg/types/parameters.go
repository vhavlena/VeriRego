package types

import (
	"sigs.k8s.io/yaml"

	"github.com/vhavlena/verirego/pkg/err"
)

type Parameter struct {
	dt       RegoTypeDef // The type of the parameter
	name     string      // The name of the parameter
	required bool        // Whether the parameter is required
}

type Parameters map[string]Parameter

// FromSpecFile creates Parameters from a YAML spec.parameters field
func FromSpecFile(yamlData []byte) (Parameters, error) {
	var data map[string]interface{}
	if unmarshalErr := yaml.Unmarshal(yamlData, &data); unmarshalErr != nil {
		return nil, err.ErrYamlUnmarshal(unmarshalErr)
	}

	spec, ok := data["spec"].(map[string]interface{})
	if !ok {
		return nil, err.ErrMissingSpecField
	}
	params, ok := spec["parameters"].([]interface{})
	if !ok {
		return nil, err.ErrInvalidParameters
	}

	result := make(Parameters)
	for _, p := range params {
		paramMap, ok := p.(map[string]interface{})
		if !ok {
			continue
		}
		name, _ := paramMap["name"].(string)
		typeStr, _ := paramMap["type"].(string)
		required, _ := paramMap["required"].(bool)

		var regoType RegoTypeDef
		switch typeStr {
		case "string":
			regoType = NewAtomicType(AtomicString)
		case "int":
			regoType = NewAtomicType(AtomicInt)
		case "boolean":
			regoType = NewAtomicType(AtomicBoolean)
		default:
			regoType = NewUnknownType()
		}

		result[name] = Parameter{
			dt:       regoType,
			name:     name,
			required: required,
		}
	}
	return result, nil
}
