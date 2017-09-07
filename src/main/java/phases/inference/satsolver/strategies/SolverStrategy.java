package phases.inference.satsolver.strategies;

import java.util.Map;
import java.util.Set;

import phases.inference.ChemTypes;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface SolverStrategy {

    boolean solveConstraints(Map<String, Set<ChemTypes>> constraints);
}
