package typesystem.elements;

import org.apache.commons.lang3.StringUtils;

import java.util.HashSet;
import java.util.Set;

import shared.Variable;
import chemical.epa.ChemTypes;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Term implements Variable {

    public final String name;
    private Set<ChemTypes> constraints = new HashSet<>();

    public Term(String name) {
        this.name = name;
    }

    @Override
    public String getVarName() {
        return this.name;
    }

    @Override
    public Set<ChemTypes> getTypingConstraints() {
        return this.constraints;
    }

    @Override
    public Variable addTypingConstraints(Set<ChemTypes> constraints) {
        this.constraints.addAll(constraints);
        return this;
    }

    @Override
    public Variable addTypingConstraint(ChemTypes constraint) {
        this.constraints.add(constraint);
        return this;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }

        Term other = (Term) obj;

        return StringUtils.equals(other.name, this.name) && this.constraints.equals(other.constraints);
    }

    public String toString() {
        return this.name + "\t" + this.constraints;
    }
}
