package symboltable;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Method extends Symbol {

    public Set<Variable> parameters = new HashSet<>();

    public Method(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public void addParameter(Variable var) {
        this.parameters.add(var);
    }

    public void addParameters(List<Variable> vars) {
        this.parameters.addAll(vars);
    }

    public void addParameters(Set<Variable> vars) {
        this.parameters.addAll(vars);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(super.toString());

        sb.append(this.parameters);

        return sb.toString();
    }
}
