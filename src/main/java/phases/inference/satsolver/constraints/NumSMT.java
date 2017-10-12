package phases.inference.satsolver.constraints;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import phases.inference.satsolver.strategies.Z3Strategy;
import typesystem.epa.ChemTypes;

/**
 * @created: 10/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NumSMT extends Constraint {

    public final static Logger logger = LogManager.getLogger(NumSMT.class);

    public NumSMT(String key, ConstraintType type) {
        super(key, type);
        logger.info("Num Key: " + this.varName);
    }

    @Override
    public String buildDeclares() {
        StringBuilder sb = new StringBuilder();
        sb.append("(declare-const ").append(varName).append(" ").append(Z3Strategy.numType).append(")").append(System.lineSeparator());
        if (!this.constraints.isEmpty()) {
            for (ChemTypes t : this.constraints) {
                // Nothing to do here.
            }
        }
        return sb.toString();
    }

    @Override
    public String buildConstraintValues() {
        StringBuilder sb = new StringBuilder();
        sb.append("; aaaaa Building asserts for: ").append(this.varName).append(NL);
        for (ChemTypes t : this.constraints) {
            sb.append("(assert (= ").append(this.varName).append(" ").append(t).append("))").append(System.lineSeparator());
        }
        return sb.toString();
    }

    @Override
    public String buildAsserts() {
        StringBuilder sb = new StringBuilder();
        for (ChemTypes t : this.constraints) {
            sb.append("(assert (= ").append(this.varName).append(" ").append(t).append("))").append(System.lineSeparator());
        }
        return sb.toString();
    }
}
