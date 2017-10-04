package phases.inference.satsolver.strategies;

import java.util.Map;

import phases.inference.satsolver.constraints.Constraint;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface SolverStrategy {

    boolean solveConstraints(Map<String, Constraint> constraints);
}
