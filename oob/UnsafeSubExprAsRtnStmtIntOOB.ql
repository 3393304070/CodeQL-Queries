/**
 * @name UnsafeSubExprAsRtnStmtIntOOB
 * @description OOB pattern where the return stmt of a function is an unsafe SubExpr
 * @kind problem
 * @problem.severity warning
 * @id UnsafeSubExprAsRtnStmtIntOOB
 * @tags maintainability
 *       codeql_queries/oob
 * @precision very-high
 */



import cpp
import semmle.code.cpp.controlflow.Guards

predicate isUnsignedType(Function f) {
    not f.getType().(IntType).isSigned()
    or f.getType().toString().matches("%unsigned%")
    or f.getType().toString().matches("%size_t%")
}

class UnsafeRtnStmtInUnsignedRtnTypeFunc extends Function {
    UnsafeRtnStmtInUnsignedRtnTypeFunc() {
        exists(Function f, SubExpr se, ReturnStmt rs |
            isUnsignedType(f)
            and rs = f.getBlock().getAStmt*()
            and rs.getExpr() = se
            and not exists(GuardCondition gc |
                        dominates(gc, se)
                        and gc.getAChild*().(VariableAccess).getTarget() = se.getAChild*().(VariableAccess).getTarget()
            )
            and this = f
        )
    }
}

from UnsafeRtnStmtInUnsignedRtnTypeFunc unsafeFunc

select unsafeFunc, "Call to " + unsafeFunc + " identified by UnsafeSubExprAsRtnStmtIntOOB.ql"
