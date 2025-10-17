/**
 * @name NullPointerAccessResetFunc
 * @description  UAF pattern specific custom reset() functions
 * @kind problem
 * @problem.severity warning
 * @id NullPointerAccessResetFunc
 * @tags maintainability
 *       codeql_queries/uaf
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

class NullPointerAccessResetFunc extends Function {
    NullPointerAccessResetFunc() {
        // Matching naming convention of such vulnerable functions
        this.getName().toLowerCase().matches("%reset%") and
        this.getAParameter().getType() instanceof PointerType and

        // Function call contains access of potentially empty pointer
        exists( FunctionCall fc |
            fc.getEnclosingFunction() = this and
            fc.getAnArgument().getAChild*() = this.getAParameter().getAnAccess()
        ) and 

        // Without checking against Null
        not exists( EqualityOperation eq |
            eq.getEnclosingFunction() = this and
            eq.getLeftOperand().getAChild*() = this.getAParameter().getAnAccess() and 
            eq.getRightOperand().(Literal).getValue().toInt() = 0
        )
    }
}

from NullPointerAccessResetFunc reset

select reset, "Call to " + reset + " identified by NullPointerAccessResetFunc.ql"
