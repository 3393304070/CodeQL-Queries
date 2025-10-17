/**
 * @name DLLDoubleFree
 * @description Double Free in Doubly Linked Lists
 * @kind problem
 * @problem.severity warning
 * @id DLLDoubleFree
 * @tags maintainability
 *       codeql_queries/uaf
 * @precision very-high
 */



import cpp

class DoublyLinkedList extends Struct {
    DoublyLinkedList() {
        exists( Struct s |
            s.getAMemberVariable().getName().matches("%next%") and
            s.getAMemberVariable().getName().matches("%prev%") and
            this = s
        )
    }
}

class DLLDoubleFreeFunc extends Function {
    DLLDoubleFreeFunc() {
        exists( FunctionCall fc, DoublyLinkedList list, TypedefType tdt | 
            this = fc.getEnclosingFunction() and
            fc.getTarget().getName().matches("%free%") and
            tdt.getBaseType() = list and
            fc.getAnArgument().getType().(PointerType).getBaseType() = tdt and
            not exists( AssignExpr assign |
                dominates(assign, fc)
                and assign.getLValue().(PointerFieldAccess).getTarget().getName().matches("%prev%")
                and assign.getLValue().(PointerFieldAccess).getQualifier().(PointerFieldAccess).getTarget().getName().matches("%next%")
                and assign.getRValue().getValue().toInt() = 0
            )
        )
    }
}

from DLLDoubleFreeFunc f
select f, "Call to " + f + " identified by DLLDoubleFree.ql"
