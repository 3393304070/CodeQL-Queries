/**
 * @name UnsafeAddExprIntOOB
 * @description OOB pattern specific to unsafe AddExpr with unsigned typed operands
 * @kind problem
 * @problem.severity warning
 * @id UnsafeAddExprIntOOB
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

predicate isUnsignedType(VariableAccess va) {
    not va.getTarget().getType().(IntType).isSigned()
    or va.getTarget().getType().toString().matches("%unsigned%")
    or va.getTarget().getType().toString().matches("%size_t%")
}

class UnsafeAddExprIntOOB extends RelationalOperation {
    UnsafeAddExprIntOOB() {
        exists(RelationalOperation ro, AddExpr ae |
            ro.getAnOperand() = ae
            and forall( | 
                isUnsignedType(ae.getAnOperand())
            )
            and this = ro
        )
    }
}

from UnsafeAddExprIntOOB unsafeAddExpr

select unsafeAddExpr.getEnclosingFunction(), "Call to " + unsafeAddExpr.getEnclosingFunction() + " identified by UnsafeAddExprIntOOB.ql"
