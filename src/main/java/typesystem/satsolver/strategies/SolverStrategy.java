package typesystem.satsolver.strategies;

import org.apache.commons.lang3.StringUtils;

import java.util.Map;

import chemical.epa.ChemTypes;
import ir.Statement;
import shared.variable.Variable;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface SolverStrategy {

    String NL = System.lineSeparator();
    String TAB = "\t";

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

    // boolean solveConstraints(Map<String, SMTSolver> constraints);
    boolean solveConstraints(Map<Integer, Statement> instructions, Map<String, Variable> variables);
}
