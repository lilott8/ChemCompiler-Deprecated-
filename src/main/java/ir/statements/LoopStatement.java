package ir.statements;

import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class LoopStatement extends BaseConditional {

    public static final String INSTRUCTION = "LOOP";

    public LoopStatement(String condition) {
        super(INSTRUCTION, condition);
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
        StringBuilder sb = new StringBuilder("");
        return sb.toString();
    }

    public String print(String indent) {
        indent += "\t";
        StringBuilder sb = new StringBuilder("");
        sb.append("Loop True Branch(").append(this.id).append(") :").append(NL);
        for(Statement s : this.trueBranch) {
            sb.append(indent).append("(").append(this.id).append(") ").append(s.print(indent)).append(NL);
        }
        return sb.toString();
    }

    public String toString() {
        StringBuilder sb = new StringBuilder("");
        sb.append("Loop True Branch: ").append(NL);
        for(Statement s : this.trueBranch) {
            sb.append("\t").append(s).append(NL);
        }
        return sb.toString();
    }
}
