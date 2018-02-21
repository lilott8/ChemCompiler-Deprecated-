package typesystem.satsolver.constraints;

import shared.Variable;
import typesystem.elements.Formula;

import static typesystem.satsolver.strategies.SolverStrategy.NL;


/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Composer {

    String compose(Formula instruction);
    String compose(Variable variable);

    default String killSwitch() {
        return "; Nuke it from orbit!" + NL + "(assert (= true false))" + NL;
    }
}
