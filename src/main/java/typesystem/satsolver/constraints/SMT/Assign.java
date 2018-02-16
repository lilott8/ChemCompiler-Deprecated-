package typesystem.satsolver.constraints.SMT;

import shared.variables.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.constraints.Composer;
import typesystem.satsolver.strategies.SolverStrategy;
import chemical.epa.ChemTypes;

import static typesystem.satsolver.strategies.SolverStrategy.NL;

/**
 * @created: 10/16/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Assign implements Composer {

    @Override
    public String compose(Formula instruction) {
        StringBuilder sb = new StringBuilder();

        // Only output matters here Output = arbitrary input at beginning of file.
        for (Variable v : instruction.getOutput()) {
            sb.append(this.compose(v));
        }

        return sb.toString();
    }

    @Override
    public String compose(Variable variable) {
        StringBuilder sb = new StringBuilder();

        for (ChemTypes t : variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }
}
