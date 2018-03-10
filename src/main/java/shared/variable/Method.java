package shared.variable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import ir.graph.BlockGraph;
import ir.statements.Statement;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Method {

    public static final Logger logger = LogManager.getLogger(Method.class);

    protected Set<ChemTypes> types = new HashSet<>();
    protected Set<Variable> parameters = new HashSet<>();
    protected String name;
    protected BlockGraph statements = new BlockGraph();

    public Method(String name) {
        this(name, new HashSet<>());
    }

    public Method(String name, Set<ChemTypes> type) {
        this.name = name;
        this.types.addAll(type);
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
        this.types.addAll(ret);
    }

    public boolean hasReturnTypes() {
        return !this.types.isEmpty();
    }

    public BlockGraph getBlockGraph() {
        return this.statements;
    }

    public void addStatement(Statement statement) {
        this.statements.addToBlock(statement);
    }

    public void addStatements(BlockGraph graph) {
        this.statements = graph;
    }

    public String getName() {
        return this.name;
    }

    public Set<ChemTypes> getTypes() {
        return this.types;
    }

    public Set<Variable> getParameters() {
        return this.parameters;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(super.toString());

        sb.append("\tParameters: ").append(this.parameters);

        return sb.toString();
    }
}
