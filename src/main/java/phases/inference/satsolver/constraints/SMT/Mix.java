package phases.inference.satsolver.constraints.SMT;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.List;

import phases.inference.elements.Instruction;
import phases.inference.elements.Variable;
import phases.inference.satsolver.constraints.Composer;
import phases.inference.satsolver.strategies.SolverStrategy;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;

import static phases.inference.satsolver.strategies.SolverStrategy.NL;
import static phases.inference.satsolver.strategies.SolverStrategy.TAB;
import static phases.inference.satsolver.strategies.SolverStrategy.getSMTName;

/**
 * @created: 10/16/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Mix implements Composer {

    public static final Logger logger = LogManager.getLogger(Mix.class);

    @Override
    public String compose(Instruction instruction) {
        StringBuilder sb = new StringBuilder();

        sb.append("; Building mixes for: ").append(instruction.id).append(NL);

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

        for (ChemTypes t : variable.getTypingConstraints()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getVarName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    private String buildMix(Variable output, List<Variable> input) {
        StringBuilder sb = new StringBuilder();

        // We need the form: a \in output ^ b \in output => LU(a,b) \subseteq output
        // At this point, output's set contains the look up values already.
        // So we don't need to run it here.  We still need to reference the
        // Lookup table for building the above formula, however.
        for (Variable input1 : input) {
            for (Variable input2 : input) {
                for (ChemTypes t1 : input1.getTypingConstraints()) {
                    for (ChemTypes t2 : input2.getTypingConstraints()) {
                        sb.append("(assert").append(NL);
                        sb.append(TAB).append("(=>").append(NL);
                        sb.append(TAB+TAB).append("(and").append(NL);
                        sb.append(TAB+TAB+TAB).append("(= ").append(getSMTName(input1.getVarName(), t1)).append(" true)").append(NL);
                        sb.append(TAB+TAB+TAB).append("(= ").append(getSMTName(input2.getVarName(), t2)).append(" true)").append(NL);
                        sb.append(TAB+TAB).append(")").append(NL);
                        sb.append(TAB+TAB).append("(and").append(NL);
                        for (ChemTypes t : EpaManager.INSTANCE.lookUp(t1, t2)) {
                            sb.append(TAB+TAB+TAB).append("(= ").append(getSMTName(output.getVarName(), t)).append(" true)").append(NL);
                        }
                        sb.append(TAB+TAB).append(")").append(NL);
                        //logger.info(String.format("(assert \n\t(=> \n\t\t(and \n\t\t\t(= %s %s) \n\t\t\t(= %s %s)) \n\t\t(and \n\t\t\t(= %s %s)))", getSMTName(input1.getVarName(), t1), getSMTName(output.getVarName(), t1), getSMTName(input2.getVarName(), t2), getSMTName(output.getVarName(), t2), EpaManager.INSTANCE.lookUp(t1, t2), "?"));
                        sb.append(TAB).append(")").append(NL);
                        sb.append(")").append(NL);
                    }
                }
            }
        }

        logger.info(sb);

        return sb.toString();
    }
}
