package ir.graph;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Method;
import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InvokeStatement extends BaseStatement implements Invoke {

    private Method method;

    public InvokeStatement(String name, Method method) {
        super(name);
        this.containsInvoke = true;
    }

    @Override
    public Method getMethod() {
        return this.method;
    }
}
