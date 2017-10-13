package phases.inference.satsolver.strategies;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;


import config.ConfigFactory;
import typesystem.epa.ChemTypes;
import phases.inference.satsolver.constraints.Constraint;

import static phases.inference.satsolver.constraints.Constraint.NL;
import static typesystem.epa.ChemTypes.CONST;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Z3Strategy implements SolverStrategy {

    public static final Logger logger = LogManager.getLogger(Z3Strategy.class);
    int id = 0;

    public static final String REAL = "REAL";
    public static final String NAT = "NAT";

    private Set<String> reserved = new HashSet<String>(){{
        add("const");
        add("assert");
    }};

    @Override
    public boolean solveConstraints(Map<String, Constraint> constraints) {
        StringBuilder sb = new StringBuilder();

        // Add the chemical reactivity groups
        for(Entry<Integer, ChemTypes> chem : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("; Declarations for reactive groups").append(NL);
            sb.append("(declare-const ").append(chem.getValue()).append(" Bool)").append(System.lineSeparator());
        }

        /*
         * We split them up for debugging purposes.
         * We can simply call `entry.getValue().buildOutput`
         * And we will have the entire SMT2 string.
         */
        for (Entry<String, Constraint> entry : constraints.entrySet()) {
            //logger.info(entry.getKey());
            sb.append(entry.getValue().buildDeclares());
            //sb.append(entry.getValue().buildOutput());
        }

        for (Entry<String, Constraint> entry : constraints.entrySet()) {
            //logger.info(entry.getKey());
            sb.append(entry.getValue().buildConstraintValues());
            //sb.append(entry.getValue().buildOutput());
        }

        for (Entry<String, Constraint> entry : constraints.entrySet()) {
            sb.append(entry.getValue().buildAsserts());
        }

        if (ConfigFactory.getConfig().isDebug()) {
            logger.info(sb);
        }
        // return true;
        return this.solveWithSMT2(sb.toString());
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
