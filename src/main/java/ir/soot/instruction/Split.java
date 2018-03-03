package ir.soot.instruction;

import chemical.epa.ChemTypes;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.NL;

/**
 * @created: 2/26/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Split extends Instruction {

    @Override
    public String toJSON() {
        return null;
    }

    @Override
    public String compose(Formula instruction) {
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

        for (ChemTypes t : variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    public String compose() {
        StringBuilder sb = new StringBuilder();
        for (Variable v : this.getOutput()) {
            sb.append(compose(v));
        }

        for (Variable v : this.getInput()) {
            sb.append(this.compose(v));
        }

        for (Variable v : this.getProperties()) {
            sb.append(this.compose(v));
        }

        return sb.toString();
    }
}
