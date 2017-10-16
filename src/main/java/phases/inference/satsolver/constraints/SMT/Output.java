package phases.inference.satsolver.constraints.SMT;

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
public class Output implements Composer {

    @Override
    public String compose(Instruction instruction) {
        StringBuilder sb = new StringBuilder();

        for (Variable v : instruction.getOutput()) {
            sb.append(compose(v));
        }

        for (Variable v : instruction.getInput()) {
            sb.append(compose(v));
        }

        for (Variable v: instruction.getProperties()) {
            sb.append(compose(v));
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
}
