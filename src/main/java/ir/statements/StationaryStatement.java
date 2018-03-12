package ir.statements;

import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/6/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class StationaryStatement extends BaseNop {

    public static final String INSTRUCTION = "STATIONARY";

    public StationaryStatement() {
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
        StringBuilder sb = new StringBuilder();

        sb.append(AssignStatement.VERB).append(" : {").append(Statement.NL);
        sb.append("\"ID\" : ").append(this.id).append(", ").append(Statement.NL);
        sb.append("\"Name\" : ").append(this.name).append(", ").append(Statement.NL);
        sb.append("\"TYPE\" : \"").append(INSTRUCTION).append("\"").append(Statement.NL);
        sb.append("}");

        return sb.toString();
    }
}
