package phases.inference.satsolver.strategies;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import config.ConfigFactory;
import phases.inference.ChemTypes;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Z3Strategy implements SolverStrategy {

    public static final Logger logger = LogManager.getLogger(Z3Strategy.class);
    int id = 0;

    private Set<String> reserved = new HashSet<String>(){{
        add("const");
        add("assert");
    }};


    @Override
    public boolean solveConstraints(Map<String, Set<ChemTypes>> constraints) {
        StringBuilder declares = new StringBuilder();
        StringBuilder assertBools = new StringBuilder();
        StringBuilder assertSets = new StringBuilder();

        for (Entry<Integer, ChemTypes> illegals : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            declares.append("(declare-const ").append(illegals.getValue()).append(" Bool)").append(System.lineSeparator());
            declares.append(("(assert (= ")).append(illegals.getValue()).append(" true))").append(System.lineSeparator());
        }

        // write the declarations to SMT2
        for (Entry<String, Set<ChemTypes>> constraint : constraints.entrySet()) {
            String key = StringUtils.replaceAll(constraint.getKey(), " ", "_");

            // Declare all the bools for all the variables (num vars * 68)
            for (Entry<Integer, ChemTypes> type : ChemTypes.getIntegerChemTypesMap().entrySet()) {
                if (ChemTypes.illegalCombos.containsKey(type.getValue())) {
                    declares.append("(declare-const ").append(type.getValue()).append("_")
                            .append(key).append(" Bool)").append(System.lineSeparator());

                    assertBools.append("(assert (= ").append(type.getValue()).append("_").append(key);
                    if (constraint.getValue().contains(type.getValue())) {
                        assertBools.append(" true))");
                    } else {
                        assertBools.append(" false))");
                    }
                    assertBools.append(System.lineSeparator());
                }
            }
            // Now do the intersections....
            assertSets.append("(assert ").append(System.lineSeparator()).append("\t(not").append(System.lineSeparator()).append("\t\t(and( ").append(System.lineSeparator());
            // We need to do !(constraints \cap illegals)
            for (ChemTypes t : constraint.getValue()) {
                if (t != ChemTypes.REAL && t != ChemTypes.NAT) {
                    for (ChemTypes illegal : ChemTypes.illegalCombos.get(t)) {
                        assertSets.append("\t\t\tand(").append(t).append("_").append(key).append(" ").append(illegal).append(")").append(System.lineSeparator());
                    }
                    //assertBools.append(2);
                }
            }
            assertSets.append("\t\t)").append(System.lineSeparator()).append("\t)").append(System.lineSeparator()).append(")").append(System.lineSeparator());
        }
        declares.append(assertBools).append(assertSets);
        logger.info(declares.toString());
        return solveWithSMT2(declares.toString());
    }

    /**
     * Rem'd for right now.
     * @param constraints
     * @return
     */
    // @Override
    //public boolean solveConstraints(Map<String, Set<ChemTypes>> constraints) {
    //    return this.solveWithSMT2(this.generateSMT2(constraints));
    //}

    private String generateSMT2(Map<String, Set<ChemTypes>> constraints) {
        StringBuilder sb = new StringBuilder();
        sb.append("(declare-datatypes () ((Type Nat Real Mat)))").append(System.lineSeparator());
        boolean printAssert = true;

        // Iterate the constraints table
        for (Map.Entry<String, Set<ChemTypes>> entry : constraints.entrySet()) {
            String identifier = StringUtils.remove(entry.getKey(), " ");
            if (this.reserved.contains(entry.getKey())) {
                identifier += ++id;
            }
            sb.append("(declare-const ").append(identifier).append(" Type)").append(System.lineSeparator());

            //sb.append("(");
            if (entry.getValue().size() > 1) {
                sb.append("(assert (and").append(System.lineSeparator());
                printAssert = false;
            }
            for (ChemTypes infer : entry.getValue()) {
                if (printAssert) {
                    sb.append("(assert ");
                }
                sb.append("(= ").append(identifier).append(" ").append(StringUtils.capitalize(infer.toString())).append(")").append(System.lineSeparator());
                if (printAssert) {
                    sb.append(")").append(System.lineSeparator());
                }
            }
            if (entry.getValue().size() > 1) {
                sb.append(")").append(System.lineSeparator()).append(")").append(System.lineSeparator());
            }
            //sb.append(")");
            // reset this each iteration.
            printAssert = true;
        }
        //sb.append("(check-sat)").append(System.lineSeparator());
        //sb.append("(get-model)").append(System.lineSeparator());
        if (ConfigFactory.getConfig().isDebug()) {
            logger.info(sb.toString());
        }
        return sb.toString();
    }

    private boolean solveWithSMT2(String smt2) {
        try {
            Context context = new Context();
            BoolExpr expr = context.parseSMTLIB2String(smt2, null, null, null, null);
            Solver solver = context.mkSolver();
            solver.add(expr);
            Status status = solver.check();
            // logger.info(solver.getModel());
            if (status == Status.SATISFIABLE) {
                //logger.trace("SAT!");
                return true;
            } else {
                //logger.error("UNSAT");
                return false;
            }
        } catch (Z3Exception e) {
            logger.error("There was an error solving the given constraints");
            logger.error(e);
            return false;
        }
    }
}
