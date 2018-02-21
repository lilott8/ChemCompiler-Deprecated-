package symboltable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import shared.Variable;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Method extends Variable {

    public static final Logger logger = LogManager.getLogger(Method.class);

    public Set<Variable> parameters = new HashSet<>();

    public Method(String name) {
        super(name, new HashSet<>());
    }

    public Method(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public Method(String name, Scope scope) {
        super(name, scope);
    }

    public Method(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type, scope);
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

    public void addReturnTypes(Set<ChemTypes> ret) {
        super.types.addAll(ret);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(super.toString());

        sb.append("\tParameters: ").append(this.parameters);

        return sb.toString();
    }
}
