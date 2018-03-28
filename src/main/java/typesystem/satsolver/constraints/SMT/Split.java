package typesystem.satsolver.constraints.SMT;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.constraints.SMTSolver;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.NL;

/**
 * @created: 10/16/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Split implements SMTSolver {

    public static final Logger logger = LogManager.getLogger(Split.class);

    @Override
    public String compose(Formula instruction) {
        StringBuilder sb = new StringBuilder();

        for (Variable v : instruction.getOutput()) {
            sb.append(compose(v));
        }

        for (Variable v : instruction.getInput()) {
            sb.append(compose(v));
        }

        for (Variable v : instruction.getProperties()) {
            sb.append(compose(v));
        }

        return sb.toString();
    }

    @Override
    public String compose(Variable variable) {
        StringBuilder sb = new StringBuilder();

        if (variable.getTypes().contains(ChemTypes.getMaterials()) && variable.getTypes().contains(ChemTypes.getNums())) {
            sb.append(killSwitch());
        }

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }
}
