/**
 * @name UnsafePtrDiffExprIntOOB
 * @description OOB pattern specific to unsafe PtrDiffExpr
 * @kind problem
 * @problem.severity warning
 * @id UnsafePtrDiffExprIntOOB
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

class UnsafePtrDiffExprIntOOB extends RelationalOperation {
    UnsafePtrDiffExprIntOOB() {
        exists(RelationalOperation ro, PointerDiffExpr pde |
            ro.getAnOperand() = pde
            and forall( |
                isUnsignedType(pde.getAnOperand())
            )
            and this = ro
        )
    }
}

from UnsafePtrDiffExprIntOOB unsafePtrDiffExpr
select unsafePtrDiffExpr.getEnclosingFunction(), "Call to " + unsafePtrDiffExpr.getEnclosingFunction() + " identified by UnsafePtrDiffExprIntOOB.ql"
