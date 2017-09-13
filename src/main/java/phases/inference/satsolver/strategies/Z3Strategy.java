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
import phases.inference.Constraint;

import static phases.inference.ChemTypes.CONST;
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

    public static final String numType = "Type";

    private Set<String> reserved = new HashSet<String>(){{
        add("const");
        add("assert");
    }};

    @Override
    public boolean solveConstraints(Map<String, Constraint> constraints) {
        StringBuilder sb = new StringBuilder();

        sb.append("(declare-datatypes () ((").append(numType);
        for (ChemTypes t : ChemTypes.getNums()) {
            sb.append(" ").append(t);
        }
        sb.append(")))").append(System.lineSeparator());
        for(Entry<Integer, ChemTypes> chem : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(chem.getValue()).append(" Bool)").append(System.lineSeparator());
        }

        for (Entry<String, Constraint> entry : constraints.entrySet()) {
            sb.append("(push)").append(System.lineSeparator());
            sb.append(entry.getValue().buildOutput());
            sb.append("(check-sat)").append(System.lineSeparator());
            sb.append("(pop)").append(System.lineSeparator());

        }

        if (constraints.containsKey(CONST)) {
            sb.append("(push)").append(System.lineSeparator());
            sb.append(constraints.get(CONST).buildOutput());
            sb.append("(check-sat)").append(System.lineSeparator()).append("(pop)").append(System.lineSeparator());
        }

        //logger.info(sb);
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
