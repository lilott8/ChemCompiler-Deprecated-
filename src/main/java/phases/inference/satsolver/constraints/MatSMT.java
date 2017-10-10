package phases.inference.satsolver.constraints;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;

/**
 * @created: 10/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MatSMT extends Constraint {

    public final static Logger logger = LogManager.getLogger(MatSMT.class);

    public MatSMT(String key, ConstraintType type) {
        super(key, type);
    }

    @Override
    public String buildOutput() {
        return null;
    }

    @Override
    public String buildDeclares() {
        StringBuilder sb = new StringBuilder();
        for (ChemTypes t : this.constraints) {
            sb.append("(declare-const ").append(getAssertName(t)).append(" Bool)").append(System.lineSeparator());
        }
        return sb.toString();
    }

    @Override
    public String buildConstraintValues() {
        StringBuilder sb = new StringBuilder();
        for (ChemTypes t : this.constraints) {
            sb.append("(assert (= ").append(getAssertName(t)).append(" true))").append(System.lineSeparator());
        }
        return sb.toString();
    }

    /**
     * This will build the conjunctions to prove set membership:
     * groupA \in one
     * @return
     */
    private String buildSetMembership() {
        StringBuilder sb = new StringBuilder();

        sb.append(TAB+TAB).append("(and").append(NL);
        for (ChemTypes t : this.constraints) {
            sb.append(TAB+TAB+TAB).append("(= ").append(t).append(" true)").append(NL);
        }
        // closing "and"
        sb.append(TAB+TAB).append(")").append(NL);
        // closing assert

        return sb.toString();
    }

    private String buildSubset() {
        StringBuilder sb = new StringBuilder();

        /*
         * Output:
         *  (and
         *      (=>
         *          (= x y)
         *          (= x' y')
         *      )
         *      (=>
         *          (...)
         *      )
         *  )
         */
        sb.append(TAB+TAB).append("(and").append(NL);
        Set<ChemTypes> types = EpaManager.INSTANCE.lookUp(this.constraints);
        if (!types.isEmpty()) {
            for (ChemTypes t : types) {
                sb.append(TAB+TAB+TAB).append("(=>").append(NL);
                sb.append(TAB+TAB+TAB+TAB).append("(= ").append(t).append( " true)").append(NL);
                sb.append(TAB+TAB+TAB+TAB).append("(= ").append(this.getAssertName(t)).append( " true)").append(NL);
                sb.append(TAB+TAB+TAB).append(")").append(NL);
            }
        }
        sb.append(TAB+TAB).append(")").append(NL);
        sb.append(TAB).append(")").append(NL);

        return sb.toString();
    }
    @Override
    public String buildAsserts() {
        StringBuilder sb = new StringBuilder();

        sb.append("; Building asserts for: ").append(this.varName).append(NL);

        if (this.constraints.size() > 1) {
            sb.append("(assert").append(NL);
            sb.append(TAB).append("(=>").append(NL);
            sb.append(this.buildSetMembership());
            sb.append(this.buildSubset());
            //sb.append(TAB).append(")").append(NL);
            sb.append(")").append(NL);
        } else {
            sb.append("(assert").append(NL);
            sb.append(this.buildSetMembership());
            sb.append(")");
        }

        return sb.toString();
    }
}
