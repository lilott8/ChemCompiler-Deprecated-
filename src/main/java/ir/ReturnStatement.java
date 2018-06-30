package ir;

import shared.variable.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/15/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ReturnStatement extends BaseStatement {

    public static final String INSTRUCTION = "RETURN";

    public ReturnStatement() {
        super(INSTRUCTION);
    }

    @Override
    public String toJson() {
        return null;
    }

    @Override
    public String toJson(String indent) {
        return null;
    }

    @Override
    public String compose(Formula instruction) {
        return null;
    }

    @Override
    public String compose(Variable variable) {
        return null;
    }

    @Override
    public String compose(Property property) {
        return null;
    }
}
