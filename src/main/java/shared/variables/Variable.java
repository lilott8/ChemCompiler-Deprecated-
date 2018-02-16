package shared.variables;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 2/5/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Variable {

    protected String name;
    protected Set<ChemTypes> types = new HashSet<>();

    public Variable(String name) {
        this.name = name;
    }

    public Variable(String name, Set<ChemTypes> type) {
       this.name = name;
       this.types.addAll(type);
    }

    public Variable addTypingConstraints(Set<ChemTypes> constraints) {
        this.types.addAll(constraints);
        return this;
    }

    public Variable addTypingConstraint(ChemTypes constraint) {
        this.types.add(constraint);
        return this;
    }

    public String getName() {
        return this.name;
    }

    public Set<ChemTypes> getTypes() {
        return this.types;
    }

    public String toString() {
        return this.name + "\t" + this.types;
    }
}
