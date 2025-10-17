/**
 * @name UnsafeMulExprAssignment
 * @description OOB pattern specific to unsafe MulExpr is assigned to another variable
 * @kind problem
 * @problem.severity warning
 * @id UnsafeMulExprAssignment
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

predicate hasVariableComparison(Expr e, VariableAccess va) {
    e.getAChild*().(VariableAccess).getTarget() = va.getTarget()
}

predicate unsafeMulExprAssignment(MulExpr me) {
    exists(AssignExpr ass |
            ass.getRValue().getAChild*() = me
            and not exists(GuardCondition gc |
                        dominates(gc, me)
                        and hasVariableComparison(me, ass.getLValue())
                        and hasVariableComparison(me, ass.getRValue().getAChild+())
            )
    )
}

predicate unsafeMulExprInitializer(MulExpr me) {
    exists(Variable v |
            v.getInitializer().getExpr().getAChild*() = me
            and not exists(GuardCondition gc |
                        dominates(gc, me)
                        and hasVariableComparison(me, v.getAnAccess())
                        and hasVariableComparison(me, v.getAnAccess())
            )
    )
}

from MulExpr me
where unsafeMulExprAssignment(me)
or unsafeMulExprInitializer(me)
select me.getEnclosingFunction(), "Call to " + me.getEnclosingFunction() + " identified by UnsafeMulExprAssignment.ql"
