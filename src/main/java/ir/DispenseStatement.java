package ir;

import shared.variable.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 6/29/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DispenseStatement extends BaseStatement {

    public static final String INSTRUCTION = "DISPENSE";

    public DispenseStatement() {
        super(INSTRUCTION);
    }

    @Override
    public String compose(Formula instruction) {
        return defaultCompose(instruction);
    }

    @Override
    public String compose(Variable variable) {
        return defaultCompose(variable);
    }

    @Override
    public String compose(Property property) {
        return defaultCompose(property);
    }

    @Override
    public String toJson(String indent) {
        return this.toJson("");
    }

    @Override
    public String toJson() {
        StringBuilder sb = new StringBuilder();

        sb.append("{").append(NL);
        sb.append("\"OPERATION\":").append("{").append(NL);
        sb.append("\"NAME\":").append("\"VARIABLE_DECLARATION\",").append(NL);
        sb.append("\"ID\":").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\":").append("\"VARIABLE\",").append(NL);
        sb.append("\"INPUTS\":").append("[").append(NL);
        Variable v = this.inputVariables.get(0);
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\": \"VARIABLE\",").append(NL);
        sb.append("\"VARIABLE\":").append("{").append(NL);
        sb.append("\"NAME\": ").append("\"").append(v.getName()).append("\"");
        if (!this.properties.isEmpty()) {
            sb.append(",").append(NL);
            if (this.properties.containsKey(Property.VOLUME)) {
                sb.append("\"VOLUME\" : {").append(NL);
                sb.append("\"VALUE\" : ").append(this.properties.get(Property.VOLUME).getValue()).append(",").append(NL);
                sb.append("\"UNITS\" : ").append("\"mL\"").append(NL);
                sb.append("}").append(NL);
            }
        } else {
            sb.append(",").append(NL);
            sb.append("\"VOLUME\" : {").append(NL);
            sb.append("\"VALUE\" : ").append(10).append(",").append(NL);
            sb.append("\"UNITS\" : ").append("\"mL\"").append(NL);
            sb.append("}").append(NL);
            sb.append("}").append(NL);
        }
        // closing variable
        sb.append("}").append(NL);
        // input closing
        sb.append("}").append(NL);

        // inputs
        sb.append("],").append(NL);
        sb.append("\"OUTPUTS\" : [").append(NL);
        // Open the tag.
        sb.append("{").append(NL);
        sb.append(this.outputVariables.get(0).redeclare());
        // Close the open tag.
        sb.append("}").append(NL);
        sb.append("]").append(NL);
        // operation
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }

}
