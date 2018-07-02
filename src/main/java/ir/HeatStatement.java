package ir;


import shared.properties.Property;
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
    public String compose(Property property) {
        return super.defaultCompose(property);
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    @Override
    public String toJson(String indent) {
        StringBuilder sb = new StringBuilder();

        // Open object brace.
        sb.append("{").append(NL);
        sb.append("\"OPERATION\" :").append(NL);
        // Open operation brace.
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"HEAT\",").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"HEAT\",").append(NL);
        sb.append("\"INPUTS\" : [").append(NL);
        // The Variable.
        // sb.append("{").append(NL);
        // sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append(this.inputVariables.get(0).buildUsage()).append(",").append(NL);
        // The Temperature.
        sb.append(this.properties.get(Property.TEMP).buildUsage());

        if (this.properties.containsKey(Property.TIME)) {
            sb.append(",");
            sb.append(this.properties.get(Property.TIME).buildUsage());
        }

        sb.append("],").append(NL);
        sb.append("\"OUTPUTS\" : []").append(NL);
        // Close operation brace.
        sb.append("}").append(NL);
        // Close object brace.
        sb.append("}").append(NL);

        return sb.toString();
    }
}
