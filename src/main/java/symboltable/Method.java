package symboltable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

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

    public static final Logger logger = LogManager.getLogger(Method.class);

    public Set<Symbol> parameters = new HashSet<>();

    public Method(String name) {
        super(name, new HashSet<>());
    }

    public Method(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public void addParameter(Variable var) {
        this.parameters.add(var);
    }

    public void addParameters(List<Symbol> vars) {
        this.parameters.addAll(vars);
    }

    public void addParameters(Set<Symbol> vars) {
        this.parameters.addAll(vars);
    }

    public void addReturnTypes(Set<ChemTypes> ret) {
        super.type.addAll(ret);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(super.toString());

        sb.append("\tParameters: ").append(this.parameters);

        return sb.toString();
    }
}
