package phases.inference.satsolver.constraints;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Map;
import java.util.Set;

import shared.substances.ChemAxonCompound;
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
        //logger.info("Mat Key: " + this.varName);
    }

    @Override
    public String buildOutput() {
        return null;
    }

    @Override
    public String buildDeclares() {
        StringBuilder sb = new StringBuilder();
        sb.append("; MAT Declarations for ").append(this.varName).append(NL);
        sb.append("(declare-const ").append(this.varName).append(" Bool)").append(NL);
        for (Map.Entry<Integer, ChemTypes> entry : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(getAssertName(entry.getValue())).append(" Bool)").append(NL);
        }
        for (ChemTypes t : this.constraints) {
            //sb.append("(declare-const ").append(getAssertName(t)).append(" Bool)").append(System.lineSeparator());
        }
        return sb.toString();
    }

    @Override
    public String buildConstraintValues() {
        StringBuilder sb = new StringBuilder();
        // Guarantee the MAT is a MAT.
        // (assert (not (or (= [MAT_REAL] true) (= [MAT_NAT] true) )))
        sb.append("(assert").append(NL+TAB).append("(not").append(NL).append(TAB+TAB)
                .append("(or").append(NL).append(TAB+TAB+TAB)
                .append("(= ").append(this.getAssertName(ChemTypes.REAL)).append(" true)")
                .append(NL).append(TAB+TAB+TAB)
                .append("(= ").append(this.getAssertName(ChemTypes.NAT)).append(" true)")
                .append(NL).append(TAB+TAB).append(")").append(NL).append(TAB).append(")").append(NL).append(")").append(NL);
        for (ChemTypes t : this.constraints) {
            //sb.append("(assert (= ").append(getAssertName(t)).append(" true))").append(System.lineSeparator());
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
        return "";
        //return sb.toString();
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

        return "";
        //return sb.toString();
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
        return "";
        //return sb.toString();
    }


}
