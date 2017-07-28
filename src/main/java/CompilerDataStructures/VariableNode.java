package CompilerDataStructures;

import java.io.Serializable;

import variable.Reference;
import variable.Variable;

/**
 * Created by chriscurtis on 10/12/16.
 */
public class VariableNode implements Serializable {
    public enum VariableType {ROOT_DECLARATION,INSTRUCTION_DECLARATION}

    private VariableType __declarationType;
    private int __craetedInOperation;
    private Variable __variable;

    public VariableNode(VariableType type, Variable variable) {
        this.__declarationType = type;
        this.__variable = variable;
        this.__craetedInOperation = -1;
    }

    public Variable getVariable() { return __variable; }

    public void setOperationID(int id) { __craetedInOperation = id; }
    public Boolean isRootDeclaration() { return __declarationType == VariableType.ROOT_DECLARATION; }
    public Boolean isInstructionDeclaration() {return __declarationType == VariableType.INSTRUCTION_DECLARATION; }
    public Boolean isRefererence() {
        return __variable instanceof Reference;
    }
}
