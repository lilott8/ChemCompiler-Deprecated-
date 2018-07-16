package typesystem.satsolver.strategies;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import chemical.epa.ChemTypes;
import config.ConfigFactory;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.rules.Rule;
import typesystem.satsolver.constraints.SMT.Assign;
import typesystem.satsolver.constraints.SMT.Branch;
import typesystem.satsolver.constraints.SMT.Detect;
import typesystem.satsolver.constraints.SMT.Heat;
import typesystem.satsolver.constraints.SMT.Math;
import typesystem.satsolver.constraints.SMT.Mix;
import typesystem.satsolver.constraints.SMT.Output;
import typesystem.satsolver.constraints.SMT.Split;
import typesystem.satsolver.constraints.SMTSolver;

import static chemical.epa.ChemTypes.NAT;
import static chemical.epa.ChemTypes.REAL;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Z3Strategy implements SolverStrategy {

    public static final Logger logger = LogManager.getLogger(Z3Strategy.class);

    private Map<Integer, Formula> instructions;
    private Map<String, Variable> variables;

    private Map<Rule.InstructionType, SMTSolver> composers = new HashMap<>();

    public Z3Strategy() {
        composers.put(Rule.InstructionType.ASSIGN, new Assign());
        composers.put(Rule.InstructionType.BRANCH, new Branch());
        composers.put(Rule.InstructionType.DETECT, new Detect());
        composers.put(Rule.InstructionType.HEAT, new Heat());
        composers.put(Rule.InstructionType.MIX, new Mix());
        composers.put(Rule.InstructionType.OUTPUT, new Output());
        composers.put(Rule.InstructionType.SPLIT, new Split());
        composers.put(Rule.InstructionType.MATH, new Math());
    }

    @Override
    public boolean solveConstraints(Map<Integer, Formula> instructions, Map<String, Variable> variables) {
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

        for (Map.Entry<Integer, Formula> instruction : this.instructions.entrySet()) {
            // if (instruction instanceof MixStatement) {
            // if (instruction.getValue().type == Rule.InstructionType.MIX) {
            //logger.fatal("need to redo solveConstrains");
            sb.append(this.composers.get(instruction.getValue().type).compose(instruction.getValue()));
            // }
            // }
        }

        if (ConfigFactory.getConfig().isDebug()) {
            // logger.info(variables);
            // logger.info(statements);
            // logger.info(sb);
        }
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

        sb.append("; Initialize declares for: ").append(SolverStrategy.getSMTName(v.getName())).append(NL);
        for (Entry<Integer, ChemTypes> types : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(SolverStrategy.getSMTName(v.getName(), types.getValue())).append(" Bool)").append(NL);
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

        numbers.retainAll(v.getTypes());
        materials.retainAll(v.getTypes());

        // If we have an intersection, i.e. NAT || REAL appear in both sets,
        // And the typing constraints are > 2 (more than NAT & REAL), then
        // This program is untypeable.
        if (!numbers.isEmpty() && !materials.isEmpty()) {
            sb.append("; Kill the type typesystem for ").append(v.getName()).append(NL);
            sb.append("(assert (= true false))").append(NL);
            return sb.toString();
        }

        // Otherwise we assume correctness.
        if (v.getTypes().contains(REAL) || v.getTypes().contains(NAT)) {
            sb.append("; ").append(SolverStrategy.getSMTName(v.getName())).append(" is a NUMBER").append(NL);
            isMat = false;
        } else {
            sb.append("; ").append(SolverStrategy.getSMTName(v.getName())).append(" is a MAT").append(NL);
            isMat = true;
        }

        sb.append("(assert").append(NL);
        if (isMat) {
            sb.append(TAB).append("(not").append(NL);
        }
        sb.append(TAB + TAB).append("(or").append(NL)
                .append(TAB + TAB + TAB).append("(= ").append(SolverStrategy.getSMTName(v.getName(), REAL))
                .append(" true)").append(NL)
                .append(TAB + TAB + TAB).append("(= ").append(SolverStrategy.getSMTName(v.getName(), NAT))
                .append(" true)").append(NL);
        if (isMat) {
            sb.append(TAB + TAB).append(")").append(NL);
        }
        sb.append(TAB).append(")").append(NL).append(")").append(NL);

        return sb.toString();
    }

    private boolean solveWithSMT2(String smt2) {
        try {
            Context context = new Context();
            BoolExpr expr = context.parseSMTLIB2String(smt2, null, null, null, null);
            Solver solver = context.mkSolver();
            solver.add(expr);
            Status status = solver.check();
            if (status == Status.SATISFIABLE) {
                logger.trace("This BioScript program is safe.");
                return true;
                //if (ConfigFactory.getConfig().isDebug()) {
                //}
            } else {
                logger.error("This BioScript may be unsafe for execution, halting compilation.");
                return false;
                //if (ConfigFactory.getConfig().isDebug()) {
                // logger.info(smt2);
                //}
            }
        } catch (Z3Exception e) {
            logger.error("There was an error solving the given constraints");
            logger.error(e);
            return false;
        }
    }
}
