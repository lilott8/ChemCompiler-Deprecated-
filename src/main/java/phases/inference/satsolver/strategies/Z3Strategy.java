package phases.inference.satsolver.strategies;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;


import config.ConfigFactory;
import phases.inference.ChemTypes;

import static phases.inference.ChemTypes.NAT;
import static phases.inference.ChemTypes.REAL;

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
        StringBuilder declareConst = new StringBuilder();
        StringBuilder initAsserts = new StringBuilder();
        StringBuilder intersections = new StringBuilder();

        // Add all the reactive group constants (Acids, Bases, etc.)
        declareConst.append(this.buildVariableDeclarations(""));
        // Add all the variables that exist. (a_Acids, a_Bases, etc.)
        for (Entry<String, Set<ChemTypes>> constraint : constraints.entrySet()) {
            declareConst.append(this.buildVariableDeclarations(constraint.getKey()));
            if (!constraint.getValue().contains(REAL) && !constraint.getValue().contains(NAT)) {
                if (!constraint.getValue().isEmpty()) {
                    initAsserts.append(this.initializeAssertions(constraint.getKey()));
                    intersections.append(this.buildIntersections(constraint.getKey(), constraint.getValue()));
                }
            }
        }
        initAsserts.append(this.initializeAssertions(""));

        logger.info(declareConst.append(initAsserts).append(intersections).toString());
        //return true;
        return this.solveWithSMT2(declareConst.append(initAsserts).append(intersections).toString());
    }

    /**
     * Builds the declare-const statements for smt2.
     *
     * This will take the varName and append every reactive group to it
     * @param varName
     *   Name of variable
     * @return
     *   String of declare-consts.
     */
    private String buildVariableDeclarations(String varName) {
        StringBuilder sb = new StringBuilder();
        for (Entry<Integer, ChemTypes> entry : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(this.buildVarName(varName, entry.getValue().toString()))
                    .append(" Bool)").append(System.lineSeparator());
        }
        return sb.toString();
    }

    private String initializeAssertions(String varName) {
        StringBuilder sb = new StringBuilder();
        // If we have an empty string, it should default to false
        String assertAs = StringUtils.isEmpty(varName) ? "false" : "true";
        for (Entry<Integer, ChemTypes> entry : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(assert (= ").append(this.buildVarName(varName, entry.getValue().toString()))
                    .append(" ").append(assertAs).append("))").append(System.lineSeparator());
        }
        return sb.toString();
    }

    /**
     * This builds the varname for us.
     * @param name
     *  Name in the constraint table
     * @param group
     *  Group the variable belongs to
     * @return
     *  String formatted the way we want.
     */
    private String buildVarName(String name, String group) {
        String var = "";
        group = StringUtils.upperCase(group);
        if (StringUtils.isEmpty(name)) {
            var = group;
        } else {
            var = StringUtils.replaceAll(name, " ", "_") + "_" + group;
        }
        return var;
    }

    private String buildIntersections(String varName, Set<ChemTypes> constraints) {
        StringBuilder intersection = new StringBuilder();
        StringBuilder asserts = new StringBuilder();
        asserts.append("(push)").append(System.lineSeparator());

        for (ChemTypes constraint : constraints) {
            if (ChemTypes.illegalCombos.get(constraint).size() > 1) {
                String comboName = this.buildVarName(varName, constraint.toString());
                // This isn't technically necessary.
                asserts.append("(assert (= ").append(comboName).append(" true))").append(System.lineSeparator());
                // begin assert
                intersection.append("(assert").append(System.lineSeparator());
                // begin and 1
                intersection.append("\t(and").append(System.lineSeparator());
                // begin not
                intersection.append("\t\t(not").append(System.lineSeparator());
                // begin and 2
                intersection.append("\t\t\t(and").append(System.lineSeparator());
                for (ChemTypes illegal : ChemTypes.illegalCombos.get(constraint)) {
                    asserts.append("(assert (= ").append(buildVarName("", illegal.toString())).append(" true))").append(System.lineSeparator());
                    // add the actual rule here.
                    intersection.append("\t\t\t\t(= ").append(comboName).append(" ").append(illegal).append(")").append(System.lineSeparator());
                }
                // end and 2
                intersection.append("\t\t\t)").append(System.lineSeparator());
                // end not
                intersection.append("\t\t)").append(System.lineSeparator());
                // end and 1
                intersection.append("\t)").append(System.lineSeparator());
                // end assert
                intersection.append(")").append(System.lineSeparator());
            }
        }

        asserts.append(intersection);
        asserts.append("(check-sat)").append(System.lineSeparator());
        asserts.append("(pop)").append(System.lineSeparator());

        return asserts.toString();
    }

    /**
     * This method assumes that the constraints are purely material, no NAT || REAL.
     * @param key
     *  Name of the variable we are working with.
     * @param types
     *  List of possible types the variable could be.
     * @return SMT2 ready string.
     */
    private String buildChemConstraints(String key, Set<ChemTypes> types) {
        StringBuilder sb = new StringBuilder();
        boolean append = false;
        sb.append("(assert ").append(System.lineSeparator()).append("\t(and").append(System.lineSeparator());
        // We need to do !(constraints \cap illegals)
        for (ChemTypes t : types) {
            if (ChemTypes.illegalCombos.containsKey(t)) {
                for (ChemTypes illegal : ChemTypes.illegalCombos.get(t)) {
                    // (and (= x true) (= y true))
                    sb.append("\t\t(not").append(System.lineSeparator());
                    sb.append("\t\t\t(and").append(System.lineSeparator());
                    sb.append("\t\t\t\t(= ").append(t).append("_").append(key).append(" true)").append(System.lineSeparator());
                    sb.append("\t\t\t\t(= ").append(illegal).append(" true)").append(System.lineSeparator());
                    sb.append("\t\t\t)").append(System.lineSeparator());
                    sb.append("\t\t)").append(System.lineSeparator());
                }
                append = true;
            }
        }
        sb.append("\t)").append(System.lineSeparator()).append(")").append(System.lineSeparator());
        return append ? sb.toString() : "";
    }

    private String buildMixedConstraints(String key, Set<ChemTypes> types) {
        StringBuilder sb = new StringBuilder();
        // This handles the case where we have a heterogeneous set of constraints
        List<ChemTypes> differs = new ArrayList<>();

        Iterator<ChemTypes> iterator = types.iterator();
        ChemTypes t = iterator.next();

        // case of one, by definition, this has to be REAL/NAT.  Otherwise we wouldn't have gotten here.
        if (!iterator.hasNext()) {
            sb.append("(assert (= ").append(key).append(" ").append(t).append("))").append(System.lineSeparator());
        }
        else {
            while(iterator.hasNext()) {
                if (t == NAT || t == REAL) {
                    differs.add(t);
                    // remove the NAT/REAL from the constraints set
                    types.remove(t);
                }
                // finally move the iterator
                t = iterator.next();
            }
        }
        // process differs...
        for (ChemTypes a : differs) {
            sb.append("(assert (= ").append(key).append(" ").append(a).append("))").append(System.lineSeparator());
        }

        if (types.size() > 0) {
            //sb.append(buildChemConstraints(key, types));
        }
        return sb.toString();
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
                logger.trace("SAT!");
                return true;
            } else {
                logger.error("UNSAT");
                return false;
            }
        } catch (Z3Exception e) {
            logger.error("There was an error solving the given constraints");
            logger.error(e);
            return false;
        }
    }
}
