package ir.statements;

import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SourceStatement extends BaseNop implements Nop {

    public static final String INSTRUCTION = "SOURCE";

    public SourceStatement() {
        super(INSTRUCTION);
    }

    @Override
    public String compose(Formula instruction) {
        return super.defaultCompose(instruction);
    }

    @Override
    public String compose(Variable variable) {
        return super.defaultCompose(variable);
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    @Override
    public String toJson(String indent) {
        return null;
    }
}
