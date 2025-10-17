/**
 * @name VulnWrapperAllocFunc
 * @description OOB pattern where the wrapper function of an allocation function does not provide bound check
 * @kind problem
 * @problem.severity warning
 * @id VulnWrapperAllocFunc
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

class VulnWrapperMallocFunc extends Function {
    VulnWrapperMallocFunc() {
        exists(FunctionCall fc, ReturnStmt rs, FunctionCall rtnfc |
            this.getBlock().getAChild+() = rs
            and rs.getExpr() = rtnfc
            and rtnfc.getTarget().getName().matches("%alloc%")
            and this.getACallToThisFunction() = fc
            and not exists(GuardCondition gc | 
                dominates(gc, rtnfc)
                and gc.getAChild+().(VariableAccess).getTarget() = rtnfc.getAnArgument().(VariableAccess).getTarget()
            )
        )
    }
}

from VulnWrapperMallocFunc f
select f, "Call to " + f + " identified by VulnWrapperAllocFunc.ql"
