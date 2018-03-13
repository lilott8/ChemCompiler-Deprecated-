package ir.statements;


import shared.variable.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class HeatStatement extends BaseNop {

    public static final String INSTRUCTION = "HEAT";

    public HeatStatement(String name) {
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
        StringBuilder sb = new StringBuilder("");

        sb.append("{").append(NL);
        sb.append("\"OPERATION\" :").append(NL);
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"HEAT\",").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"HEAT\",").append(NL);
        sb.append("\"INPUTS\" : [").append(NL);
        // The Variable.
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append(this.inputVariables.get(0).buildReference()).append(NL);
        // Close the Variable.
        sb.append("},").append(NL);

        // The Temperature.
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"PROPERTY\",").append(NL);
        sb.append("\"TEMPERATURE\" : ");
        // Temp object.
        sb.append("{").append(NL);
        Property temp = (Property) this.properties.get(Property.TEMP);
        sb.append("\"VALUE\" : ").append(temp.getValue()).append(", ").append(NL);
        sb.append("\"UNITS\" : ").append("\"").append(temp.getUnits()).append("\"").append(NL);
        // Close temp object.
        sb.append("}").append(NL);
        // close variable.
        sb.append("}").append(NL);

        sb.append(this.propertyToJson(Property.TIME));

        sb.append("],").append(NL);
        sb.append("\"OUTPUTS\" : {}").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }
}
