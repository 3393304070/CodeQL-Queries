/**
 * @name FreePtrDereferenceExprDPtr
 * @description  Dangling Pointer where only one of two related pointers is set null
 * @kind problem
 * @problem.severity warning
 * @id FreePtrDereferenceExprDPtr
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

// Assume that two variables of pointer type within the same function are related
predicate isPossibleDanglingPtr(VariableAccess ptr1, VariableAccess ptr2) {
    ptr1.getEnclosingFunction() = ptr2.getEnclosingFunction() and
    ptr1.getType() instanceof PointerType and
    ptr2.getType() instanceof PointerType
}

from VariableAccess ptr1, VariableAccess ptr2, FreeFunctionCall free 

// Free function call has argument of a ptr dereference expr
where free.getAnArgument().(PointerDereferenceExpr).getOperand() = ptr1 and
isPossibleDanglingPtr(ptr1, ptr2) and

// After freeing, only one pointer is re-assigned
exists( AssignExpr assign | 
    assign = free.getASuccessor+() and
    assign.getLValue().(PointerDereferenceExpr).getOperand().(VariableAccess).getTarget() = ptr1.getTarget()
) 

// FP might be reduced by adding another not exists() predicate to specify 
// scenarios where the other pointer isn't re-assigned too.
// and
// not exists( AssignExpr assign | 
//     assign = free.getASuccessor+() and
//     assign.getLValue().(PointerDereferenceExpr).getOperand().getAChild*().(VariableAccess).getTarget() = ptr2.getTarget()
// )

select free.getEnclosingFunction(), "Call to " + free.getEnclosingFunction() + " identified by FreePtrDereferenceExprDPtr.ql"
