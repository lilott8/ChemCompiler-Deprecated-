package ir.soot.instruction;

import java.util.List;

import chemical.combinator.CombinerFactory;
import chemical.epa.ChemTypes;
import chemical.epa.EpaManager;
import shared.variable.Variable;
import typesystem.elements.Formula;

import static typesystem.satsolver.strategies.SolverStrategy.NL;
import static typesystem.satsolver.strategies.SolverStrategy.TAB;
import static typesystem.satsolver.strategies.SolverStrategy.getSMTName;

/**
 * @created: 2/26/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Mix extends Instruction {

    public Mix() {
        super();
    }

    @Override
    public String toJSON() {
        return null;
    }

    @Override
    public String compose(Formula instruction) {
        return null;
    }

    @Override
    public String compose(Variable variable) {
        return null;
    }

    public String compose() {
        StringBuilder sb = new StringBuilder();

        sb.append("; Building mixes for: ").append(this.id).append(NL);

        for (Variable v : this.getInput()) {
            sb.append(compose(v));
        }

        // There's only one output term here.
        for (Variable v : this.getOutput()) {
            sb.append(buildMix(v, this.getInput()));
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
                for (ChemTypes t1 : input1.getTypes()) {
                    for (ChemTypes t2 : input2.getTypes()) {
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
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input1.getScopedName(), t1)).append(" true)").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input2.getScopedName(), t2)).append(" true)").append(NL);
        sb.append(TAB + TAB).append(")").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        for (ChemTypes t : EpaManager.INSTANCE.lookUp(t1, t2)) {
            sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(output.getScopedName(), t)).append(" true)").append(NL);
        }
        sb.append(TAB + TAB).append(")").append(NL);
        //logger.info(String.format("(assert \n\t(=> \n\t\t(and \n\t\t\t(= %s %s) \n\t\t\t(= %s %s)) \n\t\t(and \n\t\t\t(= %s %s)))", getSMTName(input1.getScopedName(), t1), getSMTName(output.getScopedName(), t1), getSMTName(input2.getScopedName(), t2), getSMTName(output.getScopedName(), t2), EpaManager.INSTANCE.lookUp(t1, t2), "?"));
        sb.append(TAB).append(")").append(NL);
        sb.append(")").append(NL);

        return sb.toString();
    }
}
