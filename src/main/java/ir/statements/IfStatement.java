package ir.statements;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

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
        StringBuilder sb = new StringBuilder();

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
        StringBuilder sb = new StringBuilder();

        for (ChemTypes t : variable.getTypes()) {
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
        return null;
    }
}
