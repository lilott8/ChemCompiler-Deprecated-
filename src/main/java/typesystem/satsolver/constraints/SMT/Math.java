package typesystem.satsolver.constraints.SMT;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.constraints.SMTSolver;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.NL;

/**
 * @created: 3/22/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Math implements SMTSolver {

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

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }
}
