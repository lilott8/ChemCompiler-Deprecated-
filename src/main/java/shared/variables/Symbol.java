package shared.variables;

import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

/**
 * @created: 2/15/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Symbol extends Variable {

    private Scope scope;

    public Symbol(String name) {
        super(name);
    }

    public Symbol(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public Symbol(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type);
        this.scope = scope;
    }

    public void addScope(Scope scope) {
        this.scope = scope;
    }

    public Scope getScope() {
        return this.scope;
    }

    @Override
    public String toString() {
        return super.toString() + "\t Scope Name: " + this.scope.getName();
    }
}
