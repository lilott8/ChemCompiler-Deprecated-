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
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import typesystem.epa.ChemTypes;
import phases.inference.satsolver.constraints.Constraint;

import static phases.inference.satsolver.constraints.Constraint.NL;
import static phases.inference.satsolver.constraints.Constraint.TAB;
import static typesystem.epa.ChemTypes.CONST;
import static typesystem.epa.ChemTypes.NAT;
import static typesystem.epa.ChemTypes.REAL;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Z3Strategy implements SolverStrategy {

    public static final Logger logger = LogManager.getLogger(Z3Strategy.class);

    private Map<Integer, Instruction> instructions;
    private Map<String, Variable> variables;

    @Override
    public boolean solveConstraints(Map<Integer, Instruction> instructions, Map<String, Variable> variables) {
        this.instructions = instructions;
        this.variables = variables;

        StringBuilder sb = new StringBuilder();

        sb.append("; Initialize declares for chemtypes").append(NL);
        // Initialize the declares for the chemtrail objects.
        for (Entry<Integer, ChemTypes> chemtype : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(chemtype.getValue()).append(" Bool)").append(NL);
        }

        // Initialize declares for all terms.
        for (Entry<String, Variable> i : this.variables.entrySet()) {
            sb.append(this.buildDeclares(i.getValue()));
        }

        for (Entry<String, Variable> i : this.variables.entrySet()) {
            sb.append(this.buildAssertsForNumberMaterial(i.getValue()));
        }

        //logger.info(sb);
        return this.solveWithSMT2(sb.toString());
    }

    /**
     * This builds the (declare-const varname_x Bool) For all variables.
     *
     * @param v input variable
     *
     * @return SMT String
     */
    private String buildDeclares(Variable v) {
        StringBuilder sb = new StringBuilder();

        sb.append("; Initialize declares for: ").append(getSMTName(v.getVarName())).append(NL);
        for (Entry<Integer, ChemTypes> types : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(getSMTName(v.getVarName(), types.getValue())).append(" Bool)").append(NL);
        }

        return sb.toString();
    }

    /**
     * This builds the (assert (not (or (= NAT true) (= REAL true))) Or the opposite, for each
     * variable.
     *
     * @param v input variable
     *
     * @return SMT String
     */
    private String buildAssertsForNumberMaterial(Variable v) {
        StringBuilder sb = new StringBuilder();
        boolean isMat;

        Set<ChemTypes> numbers = new HashSet<>(ChemTypes.getNums());
        Set<ChemTypes> materials = new HashSet<>(ChemTypes.getMaterials());

        numbers.retainAll(v.getTypingConstraints());
        materials.retainAll(v.getTypingConstraints());

        // If we have an intersection, i.e. NAT || REAL appear in both sets,
        // And the typing constraints are > 2 (more than NAT & REAL), then
        // This program is untypeable.
        if (!numbers.isEmpty() && !materials.isEmpty()) {
            sb.append("; Kill the type inference for ").append(v.getVarName()).append(NL);
            sb.append("(assert (= true false))").append(NL);
            return sb.toString();
        }

        // Otherwise we assume correctness.
        if (v.getTypingConstraints().contains(REAL) || v.getTypingConstraints().contains(NAT)) {
            sb.append("; ").append(getSMTName(v.getVarName())).append(" is a NUMBER").append(NL);
            isMat = false;
        } else {
            sb.append("; ").append(getSMTName(v.getVarName())).append(" is a MAT").append(NL);
            isMat = true;
        }

        sb.append("(assert").append(NL);
        if (isMat) {
            sb.append(TAB).append("(not").append(NL);
        }
        sb.append(TAB + TAB).append("(or").append(NL)
                .append(TAB + TAB + TAB).append("(= ").append(getSMTName(v.getVarName(), REAL))
                .append(" true)").append(NL)
                .append(TAB + TAB + TAB).append("(= ").append(getSMTName(v.getVarName(), NAT))
                .append(" true)").append(NL);
        if (isMat) {
            sb.append(TAB + TAB).append(")").append(NL);
        }
        sb.append(TAB).append(")").append(NL).append(")").append(NL);

        return sb.toString();
    }

    @Override
    public boolean solveConstraints(Map<String, Constraint> constraints) {
        StringBuilder sb = new StringBuilder();

        // Add the chemical reactivity groups
        sb.append("; Declarations for reactive groups").append(NL);
        for (Entry<Integer, ChemTypes> chem : ChemTypes.getIntegerChemTypesMap().entrySet()) {
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
