package ir.soot.instruction;

import shared.variable.Method;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Invoke extends Instruction {

    public Invoke(Method method) {
        this.addTypes(method.getTypes());
    }

    @Override
    public String toJSON() {
        return null;
    }

    @Override
    public String compose(Formula instruction) {
        return null;
    }

    @Override
    public String compose(Variable variable) {
        return null;
    }
}
