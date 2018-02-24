package typesystem.satsolver.constraints.SMT;

import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.constraints.Composer;

/**
 * @created: 2/21/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Failure implements Composer {

    @Override
    public String compose(Formula instruction) {
        return killSwitch();
    }

    @Override
    public String compose(Variable variable) {
        return killSwitch();
    }
}