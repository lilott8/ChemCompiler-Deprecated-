package phases.inference.satsolver.strategies;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Map;

import phases.inference.elements.Instruction;
import phases.inference.elements.Variable;

/**
 * @created: 2/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NewZ3Strategy implements SolverStrategy {

    public static final Logger logger = LogManager.getLogger(NewZ3Strategy.class);

    @Override
    public boolean solveConstraints(Map<Integer, Instruction> instructions, Map<String, Variable> variables) {
        return false;
    }
}
