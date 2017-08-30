package phases.inference.satsolver.strategies;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Map;
import java.util.Set;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Z3Strategy implements SolverStrategy {

    public static final Logger logger = LogManager.getLogger(Z3Strategy.class);

    @Override
    public void solveConstraints(Map<String, Set<String>> constraints) {
        logger.info(constraints);
    }
}
