/**
 * @name LinuxKernelKicompleteUAF
 * @description  UAF pattern specific ki_complete() in linux kernel
 * @kind problem
 * @problem.severity warning
 * @id LinuxKernelKicompleteUAF
 * @tags maintainability
 *       codeql_queries/uaf
 * @precision very-high
 */



// This query is linux kernel context specific and it is dependent on 
// where ki_complete(), the function pointer
import cpp

// The odd inheritance is due to the nature of ki_complete being a function pointer as a member
class KicompleteFunctionCall extends PointerFieldAccess {
    KicompleteFunctionCall() {
        this.getTarget().getName() = "ki_complete"
    }
}

// The arguments of the function calls are generally the following two forms
class FCArgument extends Access {
    FCArgument() {
        this instanceof VariableAccess or
        this instanceof PointerFieldAccess
    }
}

// Assume ki_complete frees the memory (we don't know, it sometimes does)
from KicompleteFunctionCall kicomplete, FCArgument arg

// There shouldn't be access to the arg after it being freed
where kicomplete.getParent().(VariableCall).getArgument(0) = arg and
exists( Access access | 
    access.getEnclosingFunction() = arg.getEnclosingFunction() and
    access.getTarget() = arg.getTarget() and
    access.getLocation().getEndLine() > arg.getLocation().getEndLine()    
)

select kicomplete.getEnclosingFunction(), "Call to " + kicomplete.getEnclosingFunction() + " identified by LinuxKernelKicompleteUAF.ql"
