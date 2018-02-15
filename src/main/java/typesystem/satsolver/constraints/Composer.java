package typesystem.satsolver.constraints;

import typesystem.elements.Instruction;
import shared.Variable;

import static typesystem.satsolver.strategies.SolverStrategy.NL;


/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Composer {

    String compose(Instruction instruction);
    String compose(Variable variable);

    default String killSwitch() {
        return "; Nuke it from orbit!" + NL + "(assert (= true false))" + NL;
    }
}
