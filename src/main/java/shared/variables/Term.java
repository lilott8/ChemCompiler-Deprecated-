package shared.variables;

import org.apache.commons.lang3.StringUtils;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Term extends Variable {

    public Term(String name) {
        super(name);
    }

    public Term(String name, Set<ChemTypes> types) {
        super(name, types);
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

        return StringUtils.equals(other.name, this.name) && this.types.equals(other.types);
    }

    public String toString() {
        return super.toString();
    }
}
