package shared.variable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import ir.Statement;

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
    protected List<Statement> statements = new ArrayList<>();
    protected Statement returnStatement;

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

    public void addStatement(Statement statement) {
        this.statements.add(statement);
    }

    public void addStatements(List<Statement> statementList) {
        this.statements.addAll(statementList);
    }

    public Statement getReturnStatement() {
        return returnStatement;
    }

    public void setReturnStatement(Statement returnStatement) {
        this.returnStatement = returnStatement;
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

    public List<Statement> getStatements() {
        return this.statements;
    }

    public void setStatements(Statement statement) {
        this.statements.add(statement);
    }
}
