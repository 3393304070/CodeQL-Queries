/**
 * @name UseAfterUnmapFC
 * @description  UAF pattern specific unmap() functions
 * @kind problem
 * @problem.severity warning
 * @id UseAfterUnmapFC
 * @tags maintainability
 *       codeql_queries/uaf
 * @precision very-high
 */



import cpp

// Locate all unmap function calls
class UnmapFunctionCall extends FunctionCall {
    UnmapFunctionCall() {
        this.getTarget().getName().toLowerCase().matches("%unmap%")
    }
}

// The arguments of the unmap function calls are generally the following two forms
class FCArgument extends Access {
    FCArgument() {
        this instanceof VariableAccess or
        this instanceof PointerFieldAccess
    }
}

from UnmapFunctionCall ufc, FCArgument fca

// The first argument is the memory to be unmapped
where ufc.getArgument(0) = fca and 

// The unmapped memory pointer is assigned to other variables after unmapping
exists( AssignExpr assign | 
    assign.getEnclosingFunction() = ufc.getEnclosingFunction() and
    assign.getRValue().(Access).getTarget() = fca.getTarget() and
    assign.getLocation().getEndLine() > ufc.getLocation().getEndLine() and

    // and the unmapped memory pointer isn't set to Null before that assignment
    not exists (AssignExpr setNull |
        setNull.getEnclosingFunction() = ufc.getEnclosingFunction() and
        setNull.getLValue().(Access).getTarget() = fca.getTarget() and
        setNull.getRValue().(Literal).getValue().toInt() = 0 and
        setNull.getLocation().getEndLine() < assign.getLocation().getEndLine()
    )
) 

select ufc.getEnclosingFunction(), "Call to " + ufc.getEnclosingFunction() + " identified by UseAfterUnmapFC.ql"

