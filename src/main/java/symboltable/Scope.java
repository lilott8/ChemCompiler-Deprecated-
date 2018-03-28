package symboltable;

import java.util.HashMap;
import java.util.Map;

import javax.annotation.Nullable;

import shared.variable.Method;
import shared.variable.Variable;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Scope {

    Map<String, Variable> symbols = new HashMap<>();
    Map<String, Method> methods = new HashMap<>();
    private Scope parentScope = null;
    private String name;
    // Will probably never be used, but jic.
    private int frameSize = 0;
    // Will probably never be used, but jic.
    private Visibility type = Visibility.GLOBAL;
    public Scope(String name) {
        this.name = name;
    }

    public Scope(String name, Scope parentScope) {
        this.name = name;
        this.parentScope = parentScope;
    }

    public Scope(String name, Visibility type) {
        this.name = name;
        this.type = type;
    }

    public Scope(String name, Visibility type, int frameSize) {
        this.name = name;
        this.type = type;
        this.frameSize = frameSize;
    }

    public Scope addSymbol(Variable symbol) {
        this.symbols.put(symbol.getName(), symbol);
        return this;
    }

    public Scope addMethod(Method method) {
        this.methods.put(method.getName(), method);
        return this;
    }

    public String getName() {
        return name;
    }

    public Visibility getType() {
        return type;
    }

    public Map<String, Variable> getVariables() {
        return symbols;
    }

    @Nullable
    public Scope getParentScope() {
        return this.parentScope;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (this.parentScope != null) {
            sb.append("Parent scope: ").append(this.parentScope.name).append(System.lineSeparator());
        } else {
            sb.append("Parent scope: NULL").append(System.lineSeparator());
        }

        for (Map.Entry<String, Variable> entry : this.symbols.entrySet()) {
            sb.append("\t").append(entry.getKey()).append(": ").append(entry.getValue()).append(System.lineSeparator());
        }

        return sb.toString();
    }

    public enum Visibility {
        FUNCTION, GLOBAL, LOOP, BRANCH
    }
}
