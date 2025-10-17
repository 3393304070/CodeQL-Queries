/**
 * @name FunctionArgMultiplicationIntOOB
 * @description OOB pattern where an unsafe multiplication of integers is passed as arg to a function
 * @kind problem
 * @problem.severity warning
 * @id FunctionArgMultiplicationIntOOB
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards


predicate missingIntOOBMultiplicationBoundCheck(FunctionCall fc) {
    exists(MulExpr mul |
        fc.getAnArgument() = mul 
        and not exists(GuardCondition gc | 
            dominates(gc, fc)
            and gc.getAChild*().(VariableAccess).getTarget() = mul.getAChild*().(VariableAccess).getTarget()
            and (
                // Check for the two main ways to perform bound check
                gc.getAChild*() instanceof MulExpr 
                or gc.getAChild*() instanceof DivExpr
                or gc.getAChild*().isAffectedByMacro()
            )
        )
        // Avoid cases where mulexpr only consists literals
        and not exists(|mul.getAChild*() instanceof Literal)
    )
}

from FunctionCall fc
where missingIntOOBMultiplicationBoundCheck(fc)

select fc.getEnclosingFunction(), "Call to " + fc.getEnclosingFunction() + " identified by FunctionArgMultiplicationIntOOB.ql"
