package ir.graph;

import shared.variable.Method;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InvokeStatement extends BaseStatement implements Invoke {

    private Method method;

    public InvokeStatement(Method method) {
        super(method.getName());
        this.containsInvoke = true;
    }

    @Override
    public Method getMethod() {
        return this.method;
    }
}
