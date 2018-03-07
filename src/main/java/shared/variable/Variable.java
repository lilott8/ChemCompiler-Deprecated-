package shared.variable;

import org.apache.commons.lang3.StringUtils;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

/**
 * @created: 2/5/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Variable implements ScopedVariable, TypedVariable {

    protected String name;
    protected Set<ChemTypes> types = new HashSet<>();
    protected Scope scope;
    //protected Value value;

    public Variable(String name) {
        this.name = name;
    }

    public Variable(String name, Set<ChemTypes> type) {
       this.name = name;
       this.types.addAll(type);
    }

    public Variable(String name, Scope scope) {
        this.name = name;
        this.scope = scope;
    }

    public Variable(String name, Set<ChemTypes> type, Scope scope) {
        this.name = name;
        this.types.addAll(type);
        this.scope = scope;
    }

    public Variable addTypingConstraints(Set<ChemTypes> constraints) {
        this.types.addAll(constraints);
        return this;
    }

    public Variable addTypingConstraint(ChemTypes constraint) {
        this.types.add(constraint);
        return this;
    }

    /*public Variable setValue(Value value) {
        this.value = value;
        return this;
    }

    public Value getValue() {
        return this.value;
    }*/

    public void addScope(Scope scope) {
        this.scope = scope;
    }

    public Scope getScope() {
        return this.scope;
    }

    public String getName() {
        return this.name;
    }

    public String getScopedName() {
        return this.scope.getName() + "_" + this.name;
    }

    public Set<ChemTypes> getTypes() {
        return this.types;
    }

    public String toString() {
        String ret = this.name + "\t" + this.types;
        if (this.scope != null) {
            ret += "\t Scope Name: " + this.scope.getName();
        }
        return ret;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }

        Variable other = (Variable) obj;

        return StringUtils.equals(other.name, this.name) && this.types.equals(other.types);
    }
}
