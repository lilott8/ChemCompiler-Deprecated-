package compilation.datastructures.node;

import java.io.Serializable;

import variable.Reference;
import variable.Variable;

/**
 * Created by chriscurtis on 10/12/16.
 */
public class VariableNode implements Serializable, Node {
    public enum VariableType {ROOT_DECLARATION,INSTRUCTION_DECLARATION}

    private VariableType declarationType;
    private int createdInOperation;
    private Variable variable;

    public VariableNode(VariableType type, Variable variable) {
        this.declarationType = type;
        this.variable = variable;
        this.createdInOperation = -1;
    }

    public Variable getVariable() { return variable; }

    public void setOperationID(int id) { createdInOperation = id; }
    public Boolean isRootDeclaration() { return declarationType == VariableType.ROOT_DECLARATION; }
    public Boolean isInstructionDeclaration() {return declarationType == VariableType.INSTRUCTION_DECLARATION; }
    public Boolean isRefererence() {
        return variable instanceof Reference;
    }
}
