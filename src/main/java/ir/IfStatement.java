package ir;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.properties.Property;
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

    private boolean isTrue = true;

    public IfStatement(String condition, boolean isTrue) {
        super(INSTRUCTION, condition);
        this.isTrue = isTrue;
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

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    @Override
    public String compose(Property property) {
        return super.defaultCompose(property);
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
        String output = String.format("Branch(isTrue: %b) Conditional: %s\n True Branch: %s\n----\nFalse Branch: %s", this.isTrue, this.condition, this.trueBranch, this.falseBranch);
        return output;
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    @Override
    public String toJson(String indent) {
        // Open the object brace.
        StringBuilder sb = new StringBuilder();
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
        StringBuilder sb = new StringBuilder();
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
