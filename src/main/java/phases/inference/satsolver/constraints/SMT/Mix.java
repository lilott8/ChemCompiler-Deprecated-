package phases.inference.satsolver.constraints.SMT;

import java.util.List;

import phases.inference.elements.Instruction;
import phases.inference.elements.Variable;
import phases.inference.satsolver.constraints.Composer;
import phases.inference.satsolver.strategies.SolverStrategy;
import typesystem.epa.ChemTypes;

import static phases.inference.satsolver.strategies.SolverStrategy.NL;

/**
 * @created: 10/16/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Mix implements Composer {

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


        return sb.toString();
    }
}
