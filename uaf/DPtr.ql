/**
 * @name DPtr
 * @description General Dangling Pointer uaf pattern
 * @kind problem
 * @problem.severity warning
 * @id DPtr
 * @tags maintainability
 *       codeql_queries/uaf
 * @precision very-high
 */



import cpp

class FreeFunctionCall extends FunctionCall {
    FreeFunctionCall() {
        this.getTarget().getName().toLowerCase().matches("%free%")
    }
}

predicate isRelatedPtrBeforeFree(Variable ptr1, Variable ptr2, FreeFunctionCall free) {
    ptr1.getType() instanceof PointerType and
    ptr2.getType() instanceof PointerType and
    ptr1.getAnAccess().getEnclosingFunction() = ptr2.getAnAccess().getEnclosingFunction() and
    ptr1.getAnAccess().getEnclosingFunction() = free.getEnclosingFunction()
}

predicate hasAssignmentAfterFree(Variable ptr1, Variable ptr2, FreeFunctionCall free) {
    exists( AssignExpr assign | 
        free.getAnArgument().(VariableAccess).getTarget() = ptr1 and
        assign.getLValue().getAChild*().(VariableAccess) = ptr1.getAnAccess() and
        assign.getRValue().getAChild*().(VariableAccess) = ptr2.getAnAccess() and
        assign.getEnclosingFunction() = free.getEnclosingFunction() and
        // getBasicBlock reduces fp but can miss tp
        // assign.getBasicBlock() = free.getBasicBlock() and
        assign.getLocation().getEndLine() > free.getLocation().getEndLine()
    ) and 
    not exists (AssignExpr setNull |
        setNull.getEnclosingFunction() = free.getEnclosingFunction() and
        // getBasicBlock reduces fp but can miss tp
        // setNull.getBasicBlock() = free.getBasicBlock() and
        (
            setNull.getLValue().(Access) = ptr1.getAnAccess() or
            setNull.getLValue().(Access) = ptr2.getAnAccess() 
        ) and
        setNull.getRValue().(Literal).getValue().toInt() = 0
    )
}

from Variable ptr1, Variable ptr2, FreeFunctionCall free

where isRelatedPtrBeforeFree(ptr1, ptr2, free) and
(
    hasAssignmentAfterFree(ptr1, ptr2, free) or
    hasAssignmentAfterFree(ptr2, ptr1, free)
)

select free.getEnclosingFunction(), "Call to " + free.getEnclosingFunction() + " identified by DPtr.ql"
