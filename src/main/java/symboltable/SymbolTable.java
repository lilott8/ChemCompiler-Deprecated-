package symboltable;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SymbolTable {

    public static final String DEFAULT_SCOPE = "DEFAULT";

    // Maps variable name to variable class.
    private Map<String, Symbol> symbols = new HashMap<>();
    // Maps scope name to scopes.
    private Map<String, Scope> scopes = new HashMap<>();
    // Keep tabs of depth of stack.
    private Stack<Scope> scopeStack = new Stack<>();

    public SymbolTable() {
        // Add the default scope to the stack.
        Scope origins = new Scope(DEFAULT_SCOPE);
        scopeStack.push(origins);
        this.scopes.put(DEFAULT_SCOPE, origins);
    }

    public Scope newScope(String name) {
        // Create a new context and push it onto the stack.
        this.scopeStack.push(new Scope(name));
        // Save the scope in the hashmap.
        this.scopes.put(name, this.scopeStack.peek());
        // Return the new scope.
        return this.scopeStack.peek();
    }

    public Scope endScope() {
        // Remove the most recent element.
        this.scopeStack.pop();
        // Return the context we return to.
        return this.scopeStack.peek();
    }

    public void addLocal(Symbol symbol) {
        // Cache it for right now.
        Scope s = this.scopeStack.peek();

        // Add it to the scope.
        s.addSymbol(symbol);
        // Add it to the global list.
        this.symbols.put(symbol.getName(), symbol);

        // Push it back onto the stack!
        this.scopeStack.push(s);
    }

    public void addLocals(List<Symbol> symbols) {
        // Cache it for right now.
        Scope s = this.scopeStack.pop();

        for (Symbol symbol : symbols) {
            s.addSymbol(symbol);
            this.symbols.put(symbol.getName(), symbol);
        }

        // Push it back onto the stack!
        this.scopeStack.push(s);
    }

    public Map<String, Symbol> getSymbols() {
        return symbols;
    }

    public Map<String, Scope> getScopes() {
        return scopes;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<String, Symbol> entry : this.symbols.entrySet()) {
            sb.append(entry.getKey()).append(": ").append(entry.getValue()).append(System.lineSeparator());
        }
        sb.append("=========================").append(System.lineSeparator());
        for (Map.Entry<String, Scope> entry : this.scopes.entrySet()) {
            sb.append("Scope: ").append(entry.getKey()).append(": ")
                    .append(System.lineSeparator()).append(entry.getValue());
        }
        return sb.toString();
    }
}
