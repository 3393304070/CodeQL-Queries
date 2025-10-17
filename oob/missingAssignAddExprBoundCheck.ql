/**
 * @name missingAssignAddExprBoundCheck
 * @description OOB pattern where there lacks a bound check for an unsafe AssignAddExpr
 * @kind problem
 * @problem.severity warning
 * @id missingAssignAddExprBoundCheck
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

Variable getVarTarget(Expr e) {
    result = e.(VariableAccess).getTarget()
}

predicate hasVariableComparison(Expr e, VariableAccess va) {
    e.getAChild*().(VariableAccess).getTarget() = va.getTarget()
}
predicate missingIntOOBAssignAddExprBoundCheck(AssignAddExpr aae) {
    not exists(GuardCondition gc, AddExpr ae |
            dominates(gc, aae)
            and gc.getAChild+() = ae
            and hasVariableComparison(ae, aae.getLValue())
            and hasVariableComparison(ae, aae.getRValue().getAChild+())
    )    
}

predicate assignToDifferentSizeVar(Assignment a1, Assignment a2) {
    a1.getASuccessor+() = a2
    and a2.getRValue().(VariableAccess).getTarget() = a1.getLValue().(VariableAccess).getTarget()
    and not getVarTarget(a1.getLValue()).getType().getSize() = getVarTarget(a2.getLValue()).getType().getSize()
}

from Assignment a1, Assignment a2
where missingIntOOBAssignAddExprBoundCheck(a1)
and assignToDifferentSizeVar(a1, a2)
select a1.getEnclosingFunction(), "Call to " + a1.getEnclosingFunction() + " identified by missingAssignAddExprBoundCheck.ql"
