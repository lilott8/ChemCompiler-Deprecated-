package ir;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SplitStatement extends BaseStatement {

    public static final String INSTRUCTION = "SPLIT";

    public SplitStatement() {
        super(INSTRUCTION);
    }

    @Override
    public String compose(Formula instruction) {
        return super.defaultCompose(instruction);
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
        StringBuilder sb = new StringBuilder("{").append(NL);
        sb.append("\"OPERATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"SPLIT\",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"SPLIT\",").append(NL);
        sb.append("\"INPUTS\" : [").append(NL);
        sb.append("{").append(NL);
        sb.append(this.inputVariables.get(0).buildUsage()).append(NL);
        sb.append("}").append(NL);
        // Closes the open bracket.
        sb.append("],").append(NL);
        sb.append("\"OUTPUTS\" : [").append(NL);
        int splitSize = Integer.parseInt((String) this.properties.get(Property.QUANTITY).getValue());
        for (int x = 0; x <= splitSize; x++) {
            sb.append("{").append(NL);
            sb.append("\"VARIABLE\" :").append(NL);
            sb.append("{").append(NL);
            sb.append("\"ID\" : \"").append(this.outputVariable.getName()).append(x).append("\",").append(NL);
            sb.append("\"NAME\" : \"").append(this.outputVariable.getName()).append(x).append("\",").append(NL);
            sb.append("\"TYPE\" : \"CHEMICAL\",").append(NL);
            sb.append(this.inputVariables.get(0).addInferredTypes());
            if (this.properties.containsKey(Property.VOLUME)) {
                sb.append(", ").append(NL);
                sb.append("\"VOLUME\" : {}");
            }
            sb.append("}");
            sb.append("}");
            if (x < splitSize - 1) {
                sb.append(",").append(NL);
            }
            x++;
        }
        sb.append("]").append(NL);
        // There might need to be a comma in the empty quotes.
        //sb.append(this.outputVariable.buildDeclaration()).append("").append(NL);
        sb.append("}").append(NL);
        // Closes the OPERATION.
        //sb.append("}").append(NL);
        // Closes the OBJECT.
        sb.append("}").append(NL);
        return sb.toString();
    }
}
