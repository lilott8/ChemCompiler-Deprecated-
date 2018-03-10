package ir.statements;

import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class JumpStatement extends BaseStatement {

    public final static String INSTRUCTION = "JUMP";

    protected JumpStatement(String name) {
        super(name);
    }

    @Override
    public String compose(Formula instruction) {
        return super.defaultCompose(instruction);
    }

    @Override
    public String compose(Variable variable) {
        return super.defaultCompose(variable);
    }
}
