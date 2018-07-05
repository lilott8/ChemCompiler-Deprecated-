package ir;

import shared.properties.Property;
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
    public String compose(Property property) {
        return super.defaultCompose(property);
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    /**
     * Returns a string representation of the object. In general, the
     * {@code toString} method returns a string that
     * "textually represents" this object. The result should
     * be a concise but informative representation that is easy for a
     * person to read.
     * It is recommended that all subclasses override this method.
     * <p>
     * The {@code toString} method for class {@code Object}
     * returns a string consisting of the name of the class of which the
     * object is an instance, the at-sign character `{@code @}', and
     * the unsigned hexadecimal representation of the hash code of the
     * object. In other words, this method returns a string equal to the
     * value of:
     * <blockquote>
     * <pre>
     * getClass().getName() + '@' + Integer.toHexString(hashCode())
     * </pre></blockquote>
     *
     * @return a string representation of the object.
     */
    @Override
    public String toString() {
        return this.name + ": " + this.inputVariables;
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
        StringBuilder sb = new StringBuilder();
        // Start Object.
        sb.append("{").append(NL);
        sb.append("\"OPERATION\" :").append(NL);
        // Start Operation.
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"DRAIN\", ").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"OUTPUT\",").append(NL);
        // Open the input array.
        sb.append("\"INPUTS\" : [").append(NL);
        // Build the input variable.
        sb.append(this.inputVariables.get(0).buildDrain()).append(NL);
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
