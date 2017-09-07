package phases.inference.satsolver;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Map;
import java.util.Set;

import phases.inference.ChemTypes;
import phases.inference.satsolver.strategies.SolverStrategy;

/**
 * @created: 8/30/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SatSolver {

    public static final Logger logger = LogManager.getLogger(SatSolver.class);

    private SolverStrategy strategy;

    public SatSolver() {

    }

    public SatSolver setSatSolver(SolverStrategy strategy) {
        this.strategy = strategy;
        return this;
    }

    public boolean solveConstraints(Map<String, Set<ChemTypes>> constraints) {
        return this.strategy.solveConstraints(constraints);
    }

}
