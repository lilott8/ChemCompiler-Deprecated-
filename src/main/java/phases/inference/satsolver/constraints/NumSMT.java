package phases.inference.satsolver.constraints;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import phases.inference.rules.Nat;
import phases.inference.satsolver.strategies.Z3Strategy;
import typesystem.epa.ChemTypes;

import static typesystem.epa.ChemTypes.NAT;

/**
 * @created: 10/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NumSMT extends Constraint {

    public final static Logger logger = LogManager.getLogger(NumSMT.class);

    public NumSMT(String key, ConstraintType type) {
        super(key, type);
    }

    @Override
    public String buildDeclares() {
        StringBuilder sb = new StringBuilder();
        sb.append("; Number Declarations for: ").append(this.varName).append(NL);
        for (ChemTypes t : ChemTypes.getNums()) {
            sb.append("(declare-const ").append(this.getAssertName(t)).append(" Bool)").append(NL);
        }
        return sb.toString();
    }

    @Override
    public String buildConstraintValues() {
        ChemTypes opposite;
        if (this.constraints.contains(ChemTypes.REAL) && this.constraints.contains(NAT)) {
            opposite = ChemTypes.FALSE;
        } else if (this.constraints.contains(ChemTypes.REAL)){
            opposite = NAT;
        } else {
            opposite = ChemTypes.REAL;
        }

        StringBuilder sb = new StringBuilder();
        sb.append("; NUMBER Building asserts for: ").append(this.varName).append(NL);
        // If we have both NAT and REAL, we cannot.  Thus we kill satisfiability.
        if (opposite == ChemTypes.FALSE) {
            sb.append("(assert (= true false) )").append(NL);
        } else {
            sb.append("(assert").append(NL).append(TAB)
                    .append("(and").append(NL).append(TAB+TAB+TAB);
            if (opposite == NAT) {
                sb.append("(= ").append(this.getAssertName(ChemTypes.REAL)).append(" true)").append(NL).append(TAB+TAB+TAB)
                        .append("(= ").append(this.getAssertName(NAT)).append(" false)");
            } else {
                sb.append("(= ").append(this.getAssertName(ChemTypes.REAL)).append(" false)").append(NL).append(TAB+TAB+TAB)
                        .append("(= ").append(this.getAssertName(NAT)).append(" true)");
            }
            sb.append(NL).append(TAB+TAB).append(")").append(NL).append(TAB).append(")").append(NL);
        }
        return sb.toString();
    }

    @Override
    public String buildAsserts() {
        StringBuilder sb = new StringBuilder();
        for (ChemTypes t : this.constraints) {
            //sb.append("(assert (= ").append(this.varName).append(" ").append(t).append("))").append(System.lineSeparator());
        }
        return sb.toString();
    }
}
