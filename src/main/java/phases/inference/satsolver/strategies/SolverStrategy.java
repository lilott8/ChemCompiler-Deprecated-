package phases.inference.satsolver.strategies;

import org.apache.commons.lang3.StringUtils;

import java.util.Map;

import phases.inference.elements.Instruction;
import phases.inference.elements.Variable;
import typesystem.epa.ChemTypes;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface SolverStrategy {

    String NL = System.lineSeparator();
    String TAB = "\t";

    // boolean solveConstraints(Map<String, Composer> constraints);
    boolean solveConstraints(Map<Integer, Instruction> instructions, Map<String, Variable> variables);

    static String getSMTName(String key, ChemTypes t) {
        key = StringUtils.replaceAll(key, "[^A-Za-z0-9]", "_");
        key = StringUtils.replace(key, "-", "_");
        key += "_" + t;
        return key;
    }

    static String getSMTName(String key) {
        key = StringUtils.replaceAll(key, " ", "_");
        key = StringUtils.replace(key, "-", "_");
        return key;
    }
}
