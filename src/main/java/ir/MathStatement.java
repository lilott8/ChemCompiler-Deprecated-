package ir;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.properties.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

/**
 * @created: 3/22/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MathStatement extends BaseStatement {

    public static final String INSTRUCTION = "MATH";

    public MathStatement() {
        super(INSTRUCTION);
    }

    @Override
    public String compose(Formula instruction) {
        return super.defaultCompose(instruction);
    }

    @Override
    public String compose(Variable variable) {
        StringBuilder sb = new StringBuilder();

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    @Override
    public String compose(Property property) {
        return defaultCompose(property);
    }

    public String toString() {
        return "Input: " + this.inputVariables + "\t output: " + this.outputVariables;
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    @Override
    public String toJson(String indent) {
        // Open the object
        StringBuilder sb = new StringBuilder("{").append(NL);
        // Create the operation.
        sb.append("\"OPERATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"MATH\",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"MATH\",").append(NL);
        sb.append("\"INPUTS\" : [").append(NL);
        int x = 0;
        for (Variable v : this.inputVariables) {
            // Open the object tag.
            sb.append("{").append(NL);
            sb.append(v.buildUsage());
            sb.append("}").append(NL);
            if (x < this.inputVariables.size() - 1) {
                sb.append(",").append(NL);
            }
            x++;
        }
        // Closes the open bracket.
        sb.append("],").append(NL);
        sb.append("\"OUTPUTS\" : [").append(NL);
        // Open the tag.
        sb.append("{").append(NL);
        sb.append(this.outputVariables.get(0).redeclare());
        // Close the open tag.
        sb.append("}").append(NL);
        sb.append("]").append(NL);
        // Closes the OPERATION.
        sb.append("}").append(NL);
        // Closes the OBJECT.
        sb.append("}").append(NL);
        return sb.toString();
    }
}
