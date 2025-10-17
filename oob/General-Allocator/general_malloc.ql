import cpp
import semmle.code.cpp.controlflow.Guards

class MallocCall extends Call {
    MallocCall() {
        exists(VariableCall vc |
            this = vc and
            vc.getExpr().(VariableAccess).getTarget().getName().matches("%malloc%")
        ) or
        exists(FunctionCall fc |
            this = fc and
            fc.getTarget().getName().matches("%malloc%") 
        )
    }
}

// FieldAccess needs to have a priority, because there exists cases where there is access to value fields in malloc, 
// and if the struct itself exists somwhere in the GuardCondition before, simply comparing VariableAccess would report FP
predicate compareFieldAccess(Expr lhs, Expr rhs) {
    lhs.(FieldAccess).getTarget() = rhs.(FieldAccess).getTarget() and
    not exists( | lhs.(FieldAccess).getParent+() instanceof FieldAccess or
        rhs.(FieldAccess).getParent+() instanceof FieldAccess
    )
}

predicate compareVariableAccess(Expr lhs, Expr rhs) {
    lhs.(VariableAccess).getTarget() = rhs.(VariableAccess).getTarget() and
    not exists( | lhs.(VariableAccess).getParent+() instanceof FieldAccess or 
        rhs.(VariableAccess).getParent+() instanceof FieldAccess 
    )
}

// Exclude cases where all arguments are constants, helpful for BFC FP reduction
predicate malloc_OnlyLiteral_Arg(MallocCall malloc) {
    exists( | malloc.getAnArgument().getAChild*() instanceof Access)
}

// Potentially able to change MulExpr to ArithmeticOperation
predicate malloc_MulExpr_Arg(MallocCall malloc) {
    malloc.getAnArgument().getAChild*() instanceof MulExpr and
    (
        if exists(|malloc.getAnArgument().getAChild*() instanceof FieldAccess)
        then not exists( GuardCondition gc | 
            dominates(gc, malloc) and
            compareFieldAccess(gc.getAChild*(), malloc.getAnArgument().getAChild*()) and
            not gc.getAChild*() instanceof NotExpr and
            not gc instanceof Access
        )
        else not exists( GuardCondition gc | 
            dominates(gc, malloc) and
            compareVariableAccess(gc.getAChild+(), malloc.getAnArgument().getAChild*()) and
            not gc.getAChild*() instanceof NotExpr and
            not gc instanceof Access
        ) and 
        not exists( Stmt assert | 
            assert.getGeneratingMacro().getMacroName().matches("%ASSERT%") and
            compareVariableAccess(assert.getAChild+(), malloc.getAnArgument().getAChild*())
        )
    )
}

// Potentially able to change MulExpr to ArithmeticOperation

// Code is relatively redundant as we need to take FieldAccess and VariableAccess into accounts separately
predicate malloc_IndirectMulExpr_Arg(MallocCall malloc) {
    if malloc.getAnArgument().getAChild*().(FieldAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof FieldAccess or
    malloc.getAnArgument().getAChild*().(FieldAccess).getTarget().getAnAssignment().getRValue().getAChild*() instanceof FieldAccess
    then 
    (
        malloc.getAnArgument().getAChild*().(FieldAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof MulExpr or
        malloc.getAnArgument().getAChild*().(FieldAccess).getTarget().getAnAssignment().getRValue().getAChild*() instanceof MulExpr 
    ) and
    exists( MulExpr me | 
        ( 
            me = malloc.getAnArgument().getAChild*().(FieldAccess).getTarget().getInitializer().getExpr() or 
            me = malloc.getAnArgument().getAChild*().(FieldAccess).getTarget().getAnAssignment().getRValue().getAChild*() 
        ) and 
        not exists( Stmt assert | 
            assert.getGeneratingMacro().getMacroName().matches("%ASSERT%") and
           compareVariableAccess(assert.getAChild+(), me.getAChild*())
        ) and
        (
            (
                not exists( GuardCondition gc |
                    dominates(gc, me) and
                    compareFieldAccess(gc.getAChild*(), me.getAChild*()) and
                    not gc.getAChild*() instanceof NotExpr and
                    not gc instanceof Access
                )
            ) or
            (
                not exists( GuardCondition gc |
                    dominates(gc, malloc) and
                    compareFieldAccess(gc.getAChild*(), malloc.getAnArgument().getAChild*()) and
                    not gc.getAChild*() instanceof NotExpr and
                    not gc instanceof Access
                ) and 
                not exists( GuardCondition gc |
                    dominates(gc, me) and
                    compareFieldAccess(gc.getAChild*(), me.getAChild*()) and
                    not gc.getAChild*() instanceof NotExpr and
                    not gc instanceof Access
                )
            )
        )
    )
    else
    (
        malloc.getAnArgument().getAChild*().(VariableAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof MulExpr or
        malloc.getAnArgument().getAChild*().(VariableAccess).getTarget().getAnAssignment().getRValue().getAChild*() instanceof MulExpr 
    ) and
    exists( MulExpr me | 
        ( 
            me = malloc.getAnArgument().getAChild*().(VariableAccess).getTarget().getInitializer().getExpr() or 
            me = malloc.getAnArgument().getAChild*().(VariableAccess).getTarget().getAnAssignment().getRValue().getAChild*() 
        ) and 
        not exists( Stmt assert | 
            assert.getGeneratingMacro().getMacroName().matches("%ASSERT%") and
           compareVariableAccess(assert.getAChild+(), me.getAChild*())
        ) and
        (
            
            not exists( GuardCondition gc |
                dominates(gc, me) and
                compareVariableAccess(gc.getAChild+(), me.getAChild*()) and
                not gc.getAChild*() instanceof NotExpr and
                not gc instanceof Access
            ) or
            (
                not exists( GuardCondition gc |
                    dominates(gc, malloc) and
                    compareVariableAccess(gc.getAChild+(), malloc.getAnArgument().getAChild*()) and
                    not gc.getAChild*() instanceof NotExpr and
                    not gc instanceof Access
                ) and 
                not exists( GuardCondition gc |
                    dominates(gc, me) and
                    compareVariableAccess(gc.getAChild+(), me.getAChild*()) and
                    not gc.getAChild*() instanceof NotExpr and
                    not gc instanceof Access
                )
            )
        )
    )
}

predicate malloc_BitWiseOP_Arg(MallocCall malloc) {
    malloc.getAnArgument().(VariableAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof BinaryBitwiseOperation and
    not exists( GuardCondition gc | 
        dominates(gc, malloc) and
        compareVariableAccess(gc.getAChild+(), malloc.getAnArgument().getAChild*()) and
        not gc.getAChild*() instanceof NotExpr and
        not gc instanceof Access
    ) and 
    not exists( Stmt assert | 
        assert.getGeneratingMacro().getMacroName().matches("%ASSERT%") and
        compareVariableAccess(assert.getAChild+(), malloc.getAnArgument().getAChild*())
    )
}

from MallocCall malloc
where 
    (
        malloc_MulExpr_Arg(malloc) or
        malloc_IndirectMulExpr_Arg(malloc) or
        malloc_BitWiseOP_Arg(malloc)
    
    ) and
    malloc_OnlyLiteral_Arg(malloc) and
    not malloc.getLocation().getFile().getAbsolutePath().regexpMatch(".*usr.*include.*")
select malloc.getLocation().getFile().getAbsolutePath(), malloc.getEnclosingFunction(), malloc

