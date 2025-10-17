/**
 * @name FuncWithArgInitByFC
 * @description OOB pattern where an unsafe variable initialised by another function call's return value is passed as arg to another function call
 * @kind problem
 * @problem.severity warning
 * @id FuncWithArgInitByFC
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

// Variables initialised by the return value of function calls
class VarInitialisedByFC extends Variable {
    VarInitialisedByFC() {
        exists(AssignExpr ae, FunctionCall fc | 
            ae.getRValue().(ConditionalExpr).getCondition() = fc
            and ae.getLValue().getType() instanceof IntegralType
            and this = getVarTarget(ae.getLValue())
        )
    }
}

Variable getVarTarget(Expr e) {
    result = e.(VariableAccess).getTarget()
}

// Allocation funtion calls with arg of such variable
predicate fcWithArgInitByFC(FunctionCall fc, VarInitialisedByFC var) {
    exists(AssignExpr ae | 
        ae.getRValue() = fc
        and fc.getTarget().getName().matches("%alloc%")
        and getVarTarget(fc.getAnArgument().getAChild*()) = var
        and var.getAnAssignment().getEnclosingFunction() = fc.getEnclosingFunction()
    )
    // No checks for validity of such variable
    and not exists(GuardCondition gc | 
        dominates(gc, fc)
        and getVarTarget(gc.getAChild*()) = var
    )
}

from VarInitialisedByFC var, FunctionCall fc
where fcWithArgInitByFC(fc, var)
select fc.getEnclosingFunction(), "Call to " + fc.getEnclosingFunction() + " identified by FuncWithArgInitByFC.ql"
