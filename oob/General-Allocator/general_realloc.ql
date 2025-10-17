import cpp
import semmle.code.cpp.controlflow.Guards

class ReallocCall extends Call {
    ReallocCall() {
        exists(VariableCall vc |
            this = vc and
            vc.getExpr().(VariableAccess).getTarget().getName().matches("%realloc%")
        ) or
        exists(FunctionCall fc |
            this = fc and
            fc.getTarget().getName().matches("%realloc%") 
        )
    }
}

// FieldAccess needs to have a priority, because there exists cases where there is access to value fields in realloc, 
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
predicate realloc_OnlyLiteral_Arg(ReallocCall realloc) {
    exists( | realloc.getArgument(1).getAChild*() instanceof Access)
}

// Potentially able to change MulExpr to ArithmeticOperation
predicate realloc_MulExpr_Arg(ReallocCall realloc) {
    realloc.getArgument(1).getAChild*() instanceof MulExpr and
    (
        if exists(|realloc.getArgument(1).getAChild*() instanceof FieldAccess)
        then not exists( GuardCondition gc | 
            dominates(gc, realloc) and
            compareFieldAccess(gc.getAChild*(), realloc.getArgument(1).getAChild*()) and
            not gc.getAChild*() instanceof NotExpr and
            not gc instanceof Access
        )
        else not exists( GuardCondition gc | 
            dominates(gc, realloc) and
            compareVariableAccess(gc.getAChild+(), realloc.getArgument(1).getAChild*()) and
            not gc.getAChild*() instanceof NotExpr and
            not gc instanceof Access
        ) and 
        not exists( Stmt assert | 
            assert.getGeneratingMacro().getMacroName().matches("%ASSERT%") and
            compareVariableAccess(assert.getAChild+(), realloc.getArgument(1).getAChild*())
        )
    )
}

// Potentially able to change MulExpr to ArithmeticOperation

// Code is relatively redundant as we need to take FieldAccess and VariableAccess into accounts separately
predicate realloc_IndirectMulExpr_Arg(ReallocCall realloc) {
    if realloc.getArgument(1).getAChild*().(FieldAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof FieldAccess or
    realloc.getArgument(1).getAChild*().(FieldAccess).getTarget().getAnAssignment().getRValue().getAChild*() instanceof FieldAccess
    then 
    (
        realloc.getArgument(1).getAChild*().(FieldAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof MulExpr or
        realloc.getArgument(1).getAChild*().(FieldAccess).getTarget().getAnAssignment().getRValue().getAChild*() instanceof MulExpr 
    ) and
    exists( MulExpr me | 
        ( 
            me = realloc.getArgument(1).getAChild*().(FieldAccess).getTarget().getInitializer().getExpr() or 
            me = realloc.getArgument(1).getAChild*().(FieldAccess).getTarget().getAnAssignment().getRValue().getAChild*() 
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
                    dominates(gc, realloc) and
                    compareFieldAccess(gc.getAChild*(), realloc.getArgument(1).getAChild*()) and
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
        realloc.getArgument(1).getAChild*().(VariableAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof MulExpr or
        realloc.getArgument(1).getAChild*().(VariableAccess).getTarget().getAnAssignment().getRValue().getAChild*() instanceof MulExpr 
    ) and
    exists( MulExpr me | 
        ( 
            me = realloc.getArgument(1).getAChild*().(VariableAccess).getTarget().getInitializer().getExpr() or 
            me = realloc.getArgument(1).getAChild*().(VariableAccess).getTarget().getAnAssignment().getRValue().getAChild*() 
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
                    dominates(gc, realloc) and
                    compareVariableAccess(gc.getAChild+(), realloc.getArgument(1).getAChild*()) and
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

predicate realloc_BitWiseOP_Arg(ReallocCall realloc) {
    realloc.getArgument(1).(VariableAccess).getTarget().getInitializer().getExpr().getAChild*() instanceof BinaryBitwiseOperation and
    not exists( GuardCondition gc | 
        dominates(gc, realloc) and
        compareVariableAccess(gc.getAChild+(), realloc.getArgument(1).getAChild*()) and
        not gc.getAChild*() instanceof NotExpr and
        not gc instanceof Access
    ) and 
    not exists( Stmt assert | 
        assert.getGeneratingMacro().getMacroName().matches("%ASSERT%") and
        compareVariableAccess(assert.getAChild+(), realloc.getArgument(1).getAChild*())
    )
}

from ReallocCall realloc
where 
    (
        realloc_MulExpr_Arg(realloc) or
        realloc_IndirectMulExpr_Arg(realloc) or
        realloc_BitWiseOP_Arg(realloc)
    
    ) and
    realloc_OnlyLiteral_Arg(realloc) and
    not realloc.getLocation().getFile().getAbsolutePath().regexpMatch(".*usr.*include.*")
select realloc.getLocation().getFile().getAbsolutePath(), realloc.getEnclosingFunction(), realloc

