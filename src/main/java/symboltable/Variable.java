package symboltable;

import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 2/5/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Variable {

    private String name;
    private Scope scope;
    private Set<ChemTypes> type;

    public Variable(String name, Scope Scope, Set<ChemTypes> type) {
        this.scope = scope;
        this.name = name;
        this.type = type;
    }

    public Scope getScope() {
        return this.scope;
    }

    public String getName() {
        return this.name;
    }

    public Set<ChemTypes> getType() {
        return this.type;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Scope: ").append(this.scope).append("\tName: ").append(this.name).append("\t type(s): ").append(type);

        return sb.toString();
    }
}
