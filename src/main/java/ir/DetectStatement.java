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
public class DetectStatement extends BaseStatement {

    public static final String INSTRUCTION = "DETECT";

    public DetectStatement() {
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
        /*
        {
        "OPERATION" : {
          "NAME" : "Measure Fluorescence",
          "ID" : "1294012199300649831",
          "CLASSIFICATION" : "DETECT",
          "INPUTS" : [
            {
              "INPUT_TYPE" : "VARIABLE",
              "STATIONARY" : {
                "NAME" : "Heroine Enzyme"
              }
            },
            {
              "INPUT_TYPE" : "PROPERTY",
              "PROPERTY" : {
                "TIME" : {
                  "VALUE" : "30",
                  "UNITS" : "MINUTE"
                }
              }
            }
          ],
          "OUTPUTS" : [
            {
              "SENSOR_DECLARATION" : {
                "ID" : "Urine Reading",
                "NAME" : "Urine Reading",
                "TYPE" : "SENSOR"
              }
            }
          ]
        }
      }
         */
        StringBuilder sb = new StringBuilder("");
        Variable sensor = this.inputVariables.get(0);
        // Start Object.
        sb.append("{").append(NL);
        sb.append("\"OPERATION\" :").append(NL);
        // Start Operation.
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"").append(sensor.getName()).append("\", ").append(NL);
        sb.append("\"ID\" :").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"DETECT\",").append(NL);
        // Open the input array.
        sb.append("\"INPUTS\" : [").append(NL);
        Variable chemical = this.inputVariables.get(1);
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"STATIONARY\" : {").append(NL);
        sb.append("\"NAME\" : \"").append(chemical.getName()).append("\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        // don't forget the property
        if (this.properties.containsKey(Property.TIME)) {
            Property time = (Property) this.properties.get(Property.TIME);
            // The Temp
            sb.append(",{").append(NL);
            sb.append("\"INPUT_TYPE\" : \"PROPERTY\",").append(NL);
            sb.append("\"PROPERTY\" : {").append(NL);
            sb.append("\"TIME\" : ");
            // Temp object.
            sb.append("{").append(NL);
            sb.append("\"VALUE\" : ").append(time.getValue()).append(", ").append(NL);
            sb.append("\"UNITS\" : ").append("\"").append(time.getUnits()).append("\"").append(NL);
            sb.append("}").append(NL);
            sb.append("}").append(NL);
            sb.append("}").append(NL);
        }
        // Close the input array.
        sb.append("],").append(NL);
        // Add the outputs (there are none).
        sb.append("\"OUTPUTS\" : [").append(NL);
        sb.append("{").append(NL);
        sb.append("\"SENSOR_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : \"").append(this.outputVariable.getName()).append("\",").append(NL);
        sb.append("\"NAME\" : \"").append(this.outputVariable.getName()).append("\",").append(NL);
        sb.append("\"TYPE\" : \"SENSOR\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        // Close the output array.
        sb.append("]").append(NL);
        // Close Operation.
        sb.append("}").append(NL);
        // Close Object.
        sb.append("}").append(NL);

        return sb.toString();
    }
}
