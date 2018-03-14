package ir;

import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DrainStatement extends BaseStatement {

    public static final String INSTRUCTION = "DRAIN";

    public DrainStatement(String name) {
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
        /*
         {"OPERATION" : {
          "NAME" : "Drain",
          "ID" : "1294012199300649800",
          "CLASSIFICATION" : "OUTPUT",
          "INPUTS" : [
            {
              "INPUT_TYPE" : "VARIABLE",
              "STATIONARY" : {
                "NAME" : "Heroine Enzyme"
              }
            }
          ],
          "OUTPUTS" : [
          ]
        }
      }
         */
        StringBuilder sb = new StringBuilder("");
        // Start Object.
        sb.append("{").append(NL);
        sb.append("\"OPERATION\" :").append(NL);
        // Start Operation.
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"DRAIN\", ").append(NL);
        sb.append("\"ID\" :").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"OUTPUT\",").append(NL);
        // Open the input array.
        sb.append("\"INPUTS\" : [").append(NL);
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"STATIONARY\" : {").append(NL);
        sb.append("\"NAME\" : \"").append(this.inputVariables.get(0).getName()).append("\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        // Close the input array.
        sb.append("],").append(NL);
        // Add the outputs (there are none).
        sb.append("\"OUTPUTS\" : []").append(NL);
        // Close Operation.
        sb.append("}").append(NL);
        // Close Object.
        sb.append("}").append(NL);

        return sb.toString();
    }
}
