package ir;

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
        // Open the object brace.
        StringBuilder sb = new StringBuilder("");
        sb.append("{").append(NL);
        sb.append("\"OPERATION\" : {").append(NL);
        sb.append("\"NAME\" : \"IF\",").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"CFG_BRANCH\",").append(NL);
        sb.append("\"CONDITION\" : \"").append(this.condition).append("\",").append(NL);
        // Open true branch.
        sb.append("\"TRUE_BRANCH\" : [").append(NL);
        int x = 0;
        for (Statement s : this.trueBranch) {
            //sb.append("{").append(NL);
            sb.append(s.toJson());
            //sb.append("}");
            if (x < this.trueBranch.size() - 1) {
                sb.append(",");
            }
            sb.append(NL);
            x++;
        }
        // Close true branch.
        sb.append("]").append(NL);
        x = 0;
        if (!this.falseBranch.isEmpty()) {
            sb.append(",").append(NL);
            // Open false branch.
            sb.append("\"FALSE_BRANCH\" : [").append(NL);
            for (Statement s : this.falseBranch) {
                //sb.append("{").append(NL);
                sb.append(s.toJson());
                //sb.append("}");
                if (x < this.falseBranch.size() - 1) {
                    sb.append(",");
                }
                sb.append(NL);
                x++;
            }
            // Close false branch.
            sb.append("]").append(NL);
        }
        // Close Operation brace.
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        return sb.toString();
    }

    public String print(String indent) {
        indent += "\t";
        StringBuilder sb = new StringBuilder("");
        sb.append(indent).append("If True Branch(").append(this.id).append("): ").append(NL);
        for (Statement s : this.trueBranch) {
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
