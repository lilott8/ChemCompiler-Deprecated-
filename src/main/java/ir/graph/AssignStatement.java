package ir.graph;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class AssignStatement extends BaseStatement implements Assign {

    public static final String INSTRUCTION = "ASSIGN";

    Variable leftOpt;
    Statement rightOp;

    public AssignStatement(String name) {
        super(name);
    }

    @Override
    public void setLeftOp(Variable variable) {
        this.leftOpt = variable;
    }

    @Override
    public void setRightOp(Statement statement) {
        this.rightOp = statement;
    }

    @Override
    public Variable getOutputVariable() {
        return this.leftOpt;
    }

    @Override
    public Set<ChemTypes> getTypes() {
        return this.leftOpt.getTypes();
    }
}
