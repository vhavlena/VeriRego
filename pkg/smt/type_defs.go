package smt

import (
	"fmt"
	"strings"

	"github.com/vhavlena/verirego/pkg/err"
	"github.com/vhavlena/verirego/pkg/types"
)

// getTypeConstr returns the SMT type constraint function name for a given Rego type.
//
// Parameters:
//
//	tp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	string: The SMT type constraint function name.
func getTypeConstr(tp *types.RegoTypeDef) string {
	if tp.IsAtomic() {
		return "is-Atom"
	} else if tp.IsArray() {
		return "is-OArray"
	}
	return "is-OObj"
}

// getDatatypesDeclaration returns SMT-LIB datatype declarations for the supported types.
//
// Returns:
//
//	[]string: A slice of SMT-LIB datatype declaration strings.
func (t *Translator) getDatatypesDeclaration() []string {
	oatom := `
(declare-datatypes ()
	((OAtom
		(OString (str String))
		(ONumber (num Int))
		(OBoolean (bool Bool))
		ONull
	))
)`
	ogentype := `
(declare-datatypes (T)
	((OGenType
    	(Atom (atom OAtom))
    	(OObj (obj (Array String T)))
    	(OArray (arr (Array Int T)))
	))
)`
	gettypeatom := `
(declare-datatypes ()
  ((OGenTypeAtom (Atom (atom OAtom)) ))
)`
	return []string{oatom, ogentype, gettypeatom}
}

// getSortDefinitions returns SMT-LIB sort definitions up to the given maximum depth.
//
// Parameters:
//
//	maxDepth int: The maximum depth for sort definitions.
//
// Returns:
//
//	[]string: A slice of SMT-LIB sort definition strings.
func (t *Translator) getSortDefinitions(maxDepth int) []string {
	defs := make([]string, 0, maxDepth+1)
	for i := 0; i <= maxDepth; i++ {
		if i == 0 {
			defs = append(defs, "(define-sort OTypeD0 () (OGenType OGenTypeAtom))")
			continue
		}
		defs = append(defs, fmt.Sprintf("(define-sort OTypeD%d () (OGenType OTypeD%d))", i, i-1))
	}
	return defs
}

// getSmtConstrAssert generates an SMT-LIB assertion for the constraints of a value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	string: The SMT-LIB assertion string.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtConstrAssert(smtValue string, tp *types.RegoTypeDef) (string, error) {
	andArr, err2 := t.getSmtConstr(smtValue, tp)
	if err2 != nil {
		return "", err.ErrSmtConstraints(err2)
	}
	assert := strings.Join(andArr, " ")
	return fmt.Sprintf("(assert (and %s))", assert), nil
}

// getSmtConstr generates SMT-LIB constraints for a value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego type definition.
//
// Returns:
//
//	[]string: A slice of SMT-LIB constraint strings.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if tp.IsAtomic() {
		return t.getSmtAtomConstr(smtValue, tp)
	} else if tp.IsObject() {
		return t.getSmtObjectConstr(smtValue, tp)
	}
	return nil, err.ErrUnsupportedType
}

// getSmtObjectConstr generates SMT-LIB constraints for an object value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego object type definition.
//
// Returns:
//
//	[]string: A slice of SMT-LIB constraint strings for the object fields.
//	error: An error if constraints could not be generated.
func (t *Translator) getSmtObjectConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsObject() {
		return nil, err.ErrUnsupportedType
	}

	andConstr := make([]string, 0, 64)
	for key, val := range tp.ObjectFields {
		sel := fmt.Sprintf("(select (obj %s) \"%s\")", smtValue, key)
		if !val.IsAtomic() {
			andConstr = append(andConstr, fmt.Sprintf("(%s %s)", getTypeConstr(&val), sel))
		}

		valAnalysis, err2 := t.getSmtConstr(sel, &val)
		if err2 != nil {
			return nil, err.ErrSmtFieldConstraints(key, err2)
		}
		andConstr = append(andConstr, valAnalysis...)
	}
	return andConstr, nil
}

// getSmtAtomConstr generates SMT-LIB constraints for an atomic value and type.
//
// Parameters:
//
//	smtValue string: The SMT variable or value name.
//	tp *types.RegoTypeDef: The Rego atomic type definition.
//
// Returns:
//
//	[]string: A slice with a single SMT-LIB constraint string for the atomic value.
//	error: An error if the atomic type is unsupported.
func (t *Translator) getSmtAtomConstr(smtValue string, tp *types.RegoTypeDef) ([]string, error) {
	if !tp.IsAtomic() {
		return nil, err.ErrUnsupportedType
	}

	switch tp.AtomicType {
	case types.AtomicString:
		return []string{fmt.Sprintf("(is-OString (atom %s))", smtValue)}, nil
	case types.AtomicInt:
		return []string{fmt.Sprintf("(is-ONumber (atom %s))", smtValue)}, nil
	case types.AtomicBoolean:
		return []string{fmt.Sprintf("(is-OBoolean (atom %s))", smtValue)}, nil
	default:
		return nil, err.ErrUnsupportedAtomic
	}
}
