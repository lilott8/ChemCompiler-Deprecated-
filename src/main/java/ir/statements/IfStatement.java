package ir.statements;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class IfStatement extends BaseConditional {

    public static final Logger logger = LogManager.getLogger(IfStatement.class);

    public static final String INSTRUCTION = "IF";

    public IfStatement(String condition) {
        super(INSTRUCTION, condition);
        logger.warn("Why is the condition coming in as a string?");
    }

    @Override
    public String compose(Formula instruction) {
        StringBuilder sb = new StringBuilder("");

        for (Variable v : instruction.getInput()) {
            sb.append(compose(v));
            //sb.append(this.formInputSMT(v));
        }

        for (Variable v : instruction.getOutput()) {
            //sb.append(this.formOutputSMT(v));
            sb.append(compose(v));
        }

        return sb.toString();
    }

    @Override
    public String compose(Variable variable) {
        StringBuilder sb = new StringBuilder("");

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
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
        sb.append(indent).append("If True Branch(").append(this.id).append("): ").append(NL);
        for(Statement s : this.trueBranch) {
            sb.append("(").append(this.id).append(") ").append(s.print(indent)).append(NL);
        }
        if (!this.falseBranch.isEmpty()) {
            sb.append("If False Branch(").append(this.id).append("): ").append(NL);
            for (Statement s : this.falseBranch) {
                sb.append(indent).append("(").append(this.id).append(") ").append(s.print(indent)).append(NL);
            }
        }
        return sb.toString();
    }
}
