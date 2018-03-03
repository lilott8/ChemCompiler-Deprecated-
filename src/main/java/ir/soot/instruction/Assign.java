package ir.soot.instruction;

import chemical.epa.ChemTypes;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.NL;

/**
 * @created: 2/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Assign extends Instruction {

    Instruction instruction;

    public Assign() {
        super();
    }

    public void addInstruction(Instruction instruction) {
        this.instruction = instruction;
    }

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
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    @Override
    public String toJSON() {
        return null;
    }
}
