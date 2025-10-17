/**
 * @name GetThenFreeAddrInfoUAFFunction
 * @description  UAF pattern specific to getaddrinfo() and freeaddrinfo()
 * @kind problem
 * @problem.severity warning
 * @id GetThenFreeAddrInfoUAFFunction
 * @tags maintainability
 *       codeql_queries/uaf
 * @precision very-high
 */


import cpp

Variable getVarTarget(Expr e) {
    result = e.(VariableAccess).getTarget()
}

class GetThenFreeAddrInfoUAFFunction extends Function {
    GetThenFreeAddrInfoUAFFunction() {
        // Locate all functions that calls both getaddrinfo() and freeaddrinfo()
        exists(FunctionCall getaddrinfo, FunctionCall freeaddrinfo | 
            getaddrinfo.getTarget().getName() = "getaddrinfo" and 
            freeaddrinfo.getTarget().getName() = "freeaddrinfo" and
            getVarTarget(getaddrinfo.getArgument(3).getAChild*()) = getVarTarget(freeaddrinfo.getArgument(0).getAChild*()) and
            getaddrinfo.getEnclosingFunction() = freeaddrinfo.getEnclosingFunction() and 
            this = getaddrinfo.getEnclosingFunction() and 

            // Identify whether there exists assignment of freeaddrinfo's arg
            exists(AssignExpr assign, Variable uaf, VariableAccess uafAccess |
                // Make sure such assignment takes place between both calls
                assign.getEnclosingFunction() = this and
                assign.getLocation().getEndLine() > getaddrinfo.getLocation().getEndLine() and
                assign.getLocation().getEndLine() < freeaddrinfo.getLocation().getEndLine() and

                getVarTarget(assign.getLValue()) = uaf and
                getVarTarget(assign.getRValue()) = getVarTarget(freeaddrinfo.getArgument(0).getAChild*()) and

                // Identify whether the LValue of such assignment is accessed after calling freeaddrinfo()
                uafAccess.getEnclosingFunction() = this and
                uafAccess = uaf.getAnAccess() and
                uafAccess.getLocation().getEndLine() > freeaddrinfo.getLocation().getEndLine() and

                // If the access is only a check against Null, there's no risk for UAF
                exists(| not uafAccess.getParent() instanceof NotExpr)
            )
        )
    }
}

from GetThenFreeAddrInfoUAFFunction f 
select f, "Call to " + f + " identified by GetThenFreeAddrInfoUAFFunction.ql"
