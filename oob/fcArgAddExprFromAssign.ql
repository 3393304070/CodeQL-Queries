/**
 * @name fcArgAddExprFromAssign
 * @description OOB pattern where an argument to a function call is assigned by an unsafe AddExpr
 * @kind problem
 * @problem.severity warning
 * @id fcArgAddExprFromAssign
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

class MemoryFunctionCall extends FunctionCall {
  MemoryFunctionCall() { this.getTarget().getName().matches("%alloc%") or
    this.getTarget().getName().matches("%cpy%") or
    this.getTarget().getName().matches("%mem%")
  }
}

predicate fcArgAddExprFromAssign (FunctionCall fc) {
  exists(AssignExpr ass, AddExpr ae | 
    fc.getAnArgument().getAChild*() = ae
    and ass.getLValue().(VariableAccess).getTarget() = ae.getAnOperand().(VariableAccess).getTarget()
    and fc.getEnclosingFunction() = ass.getEnclosingFunction()
    and not exists(GuardCondition gc |
      dominates(gc, fc)
      and gc.getAChild*().(VariableAccess).getTarget() = ass.getLValue().(VariableAccess).getTarget()
    )
  )
}

from MemoryFunctionCall mfc
where fcArgAddExprFromAssign(mfc)
select mfc.getEnclosingFunction(), "Call to " + mfc.getEnclosingFunction() + " identified by fcArgAddExprFromAssign.ql"
