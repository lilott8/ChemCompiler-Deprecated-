package typesystem.satsolver.constraints.SMT;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.combinator.CombinerFactory;
import chemical.epa.ChemTypes;
import chemical.epa.EpaManager;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.constraints.SMTSolver;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.NL;
import static typesystem.satsolver.strategies.SolverStrategy.TAB;
import static typesystem.satsolver.strategies.SolverStrategy.getSMTName;

/**
 * @created: 10/16/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Mix implements SMTSolver {

    public static final Logger logger = LogManager.getLogger(Mix.class);

    @Override
    public String compose(Formula instruction) {
        StringBuilder sb = new StringBuilder();

        sb.append("; Building mixes for: ").append(instruction.getId()).append(NL);

        for (Variable v : instruction.getInput()) {
            sb.append(compose(v));
        }

        // There's only one output term here.
        for (Variable v : instruction.getOutput()) {
            sb.append(buildMix(v, instruction.getInput()));
        }

        return sb.toString();
    }

    @Override
    public String compose(Variable variable) {
        StringBuilder sb = new StringBuilder();

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    private String buildMix(Variable output, List<Variable> input) {
        StringBuilder sb = new StringBuilder();

        // We need the form: a \in output ^ b \in output => LU(a,b) \subseteq output
        // At this point, output's set contains the look up values already.
        // So we don't need to run it here.  We still need to reference the
        // Lookup table for building the above formula, however.
        boolean killSwitch = false;
        for (Variable input1 : input) {
            for (Variable input2 : input) {
                for (ChemTypes t1 : (Set<ChemTypes>) input1.getTypes()) {
                    for (ChemTypes t2 : (Set<ChemTypes>) input2.getTypes()) {
                        if (!CombinerFactory.getCombiner().combine(t1, t2)) {
                            killSwitch = true;
                        }
                        sb.append(this.buildSimpleImplication(output, input1, input2, t1, t2));
                        //sb.append(this.buildSimpleImplicationWithFalses(output, input1, input2, t1, t2));
                    }
                }
            }
        }
        if (killSwitch) {
            sb.append(killSwitch());
        }
        return sb.toString();
    }


    /**
     * This is the common case! This builds the form: t1 \in output ^ t2 \in output => lu(t1, t2)
     * \subset output Which is: (assert (=> (and (= input1_t1 true) (= input2_t2 true) ) (and (=
     * output_lu(t1, t2) true) ; this will populate for each lu value ) ) )
     */
    private String buildSimpleImplication(Variable output, Variable input1, Variable input2, ChemTypes t1, ChemTypes t2) {
        StringBuilder sb = new StringBuilder();

        sb.append("(assert").append(NL);
        sb.append(TAB).append("(=>").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input1.getName(), t1)).append(" true)").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input2.getName(), t2)).append(" true)").append(NL);
        sb.append(TAB + TAB).append(")").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        for (ChemTypes t : EpaManager.INSTANCE.lookUp(t1, t2)) {
            sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(output.getName(), t)).append(" true)").append(NL);
        }
        sb.append(TAB + TAB).append(")").append(NL);
        //logger.info(String.format("(assert \n\t(=> \n\t\t(and \n\t\t\t(= %s %s) \n\t\t\t(= %s %s)) \n\t\t(and \n\t\t\t(= %s %s)))", getSMTName(input1.getName(), t1), getSMTName(output.getName(), t1), getSMTName(input2.getName(), t2), getSMTName(output.getName(), t2), EpaManager.INSTANCE.lookUp(t1, t2), "?"));
        sb.append(TAB).append(")").append(NL);
        sb.append(")").append(NL);

        return sb.toString();
    }

    /**
     * This builds the form: t1 \in output ^ t2 \in output => lu(t1, t2) \subset output Which is:
     * (assert (=> (and (= input1_t1 true) (= input2_t2 true) ) (and (= output_lu(t1, t2) true) ;
     * this will populate for each lu value. (= (allTypes \setminus output_lu(t1, t2)) false) ; all
     * types not in the lookup are false. ) ) )
     */
    private String buildSimpleImplicationWithFalses(Variable output, Variable input1, Variable input2, ChemTypes t1, ChemTypes t2) {
        StringBuilder sb = new StringBuilder();

        sb.append("(assert").append(NL);
        sb.append(TAB).append("(=>").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input1.getName(), t1)).append(" true)").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input2.getName(), t2)).append(" true)").append(NL);
        sb.append(TAB + TAB).append(")").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        Set<ChemTypes> notPresent = new HashSet<>(EpaManager.INSTANCE.lookUp(t1, t2));
        Set<ChemTypes> allTypes = new HashSet<>(ChemTypes.getAllTypes());
        for (ChemTypes t : EpaManager.INSTANCE.lookUp(t1, t2)) {
            sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(output.getName(), t)).append(" true)").append(NL);
        }
        allTypes.removeAll(notPresent);
        for (ChemTypes t : allTypes) {
            sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(output.getName(), t)).append(" false)").append(NL);
        }
        sb.append(TAB + TAB).append(")").append(NL);
        //logger.info(String.format("(assert \n\t(=> \n\t\t(and \n\t\t\t(= %s %s) \n\t\t\t(= %s %s)) \n\t\t(and \n\t\t\t(= %s %s)))", getSMTName(input1.getName(), t1), getSMTName(output.getName(), t1), getSMTName(input2.getName(), t2), getSMTName(output.getName(), t2), EpaManager.INSTANCE.lookUp(t1, t2), "?"));
        sb.append(TAB).append(")").append(NL);
        sb.append(")").append(NL);

        return sb.toString();
    }

    private String buildComplexImplication(Variable output, Variable input1, Variable input2, ChemTypes t1, ChemTypes t2) {
        StringBuilder sb = new StringBuilder();

        return sb.toString();
    }

    private String buildComplexImplicationWithFalses(Variable output, Variable input1, Variable input2, ChemTypes t1, ChemTypes t2) {
        StringBuilder sb = new StringBuilder();

        return sb.toString();
    }

    private String buildMixWithImplication(Variable output, List<Variable> input) {
        StringBuilder sb = new StringBuilder();

        boolean killSwitch = false;
        for (Variable input1 : input) {
            for (Variable input2 : input) {
                for (ChemTypes t1 : (Set<ChemTypes>) input1.getTypes()) {
                    for (ChemTypes t2 : (Set<ChemTypes>) input2.getTypes()) {

                    }
                }
            }
        }

        return sb.toString();
    }
}
