package ir.soot;

import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Method;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InvokeExpression extends Expression {

    void setMethodRef(Method method);
    Method getMethodRef();
    Method getMethod();
    List<Value> getArgs();
    int getArgCount();
    void setArg(int at, Value arg);
    ValueBox getArgBox(int at);
    Set<ChemTypes> getType();

}
