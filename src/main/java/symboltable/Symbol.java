package symboltable;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Symbol {

    protected String name;
    // Functions use this for their return value.
    protected Set<ChemTypes> type = new HashSet<>();

    protected String scope;

    public Symbol(String name, Set<ChemTypes> type) {
        this.name = name;
        this.type.addAll(type);
    }

    public void addScope(Scope scope) {
        this.scope = scope.getName();
    }

    public String getName() {
        return name;
    }

    public Set<ChemTypes> getType() {
        return type;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Name: ").append(this.name).append("\tType(s): ").append(this.type);

        return sb.toString();
    }
}
