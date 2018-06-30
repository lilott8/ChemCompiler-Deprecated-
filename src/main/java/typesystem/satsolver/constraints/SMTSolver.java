package typesystem.satsolver.constraints;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.NL;


/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface SMTSolver {

    String compose(Formula instruction);

    String compose(Variable variable);

    String compose(Property property);

    default String killSwitch() {
        return "; Nuke it from orbit!" + NL + "(assert (= true false))" + NL;
    }

    default String defaultCompose(Formula instruction) {
        StringBuilder sb = new StringBuilder();

        for (Variable v : instruction.getOutput()) {
            sb.append(compose(v));
        }

        for (Variable v : instruction.getInput()) {
            sb.append(compose(v));
        }

        for (Property v : instruction.getProperties()) {
            sb.append(compose(v));
        }

        return sb.toString();
    }

    default String defaultCompose(Variable variable) {
        StringBuilder sb = new StringBuilder();

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    default String defaultCompose(Property property) {
        return "";
    }
}
