package factory

import (
	"fmt"
	"strings"
)

func And(clauses []string) string {
	return fmt.Sprintf("(and %s)", strings.Join(clauses, " "))
}

func Type(depth int) string {
	return fmt.Sprintf("OTypeD%d", depth)
}

func Eq(v1 *string, v2 *string) string {
	return fmt.Sprintf("(= %s %s)", *v1, *v2)
}

func Ite(ifSmt *string, thenSmt *string, elseSmt *string) string {
	return fmt.Sprintf("(ite %s %s %s)", *ifSmt, *thenSmt, *elseSmt)
}

func Let(defSmt *string, exprSmt *string) string {
	return fmt.Sprintf("(let %s %s)", *defSmt, *exprSmt)
}

func Assert(exprSmt *string) string {
	return fmt.Sprintf("(assert %s)", *exprSmt)
}

func DefineFunc(funcName *string, argNames []string, bodySmt *string) string {
	args := strings.Join(argNames, " " + VarType())
	return fmt.Sprintf("(define-fun %s (%s) %s %s)",
		*funcName,			// function name
		args,
		VarType(),	// return type
		*bodySmt)
}

func VarType() string {
	return "OType"
}

