package symboltable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 2/5/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Variable extends Symbol {

    public Variable(String name, Set<ChemTypes> type) {
       super(name, type);
    }

    public String getName() {
        return this.name;
    }

    public String toString() {
        return super.toString();
    }

    public Variable addTypingConstraints(Set<ChemTypes> constraints) {
        this.type.addAll(constraints);
        return this;
    }

    public Variable addTypingConstraint(ChemTypes constraint) {
        this.type.add(constraint);
        return this;
    }

    public String getScope() {
        return this.scope;
    }
}
