package smt

import (
	"github.com/vhavlena/verirego/pkg/types"
)

// Translator is responsible for translating Rego terms to SMT expressions.
type Translator struct {
	TypeInfo *types.TypeAnalyzer // Type information for Rego terms
	VarMap   map[string]string   // Mapping of Rego term keys to SMT variable names
	smtLines []string            // Collected SMT lines
}
