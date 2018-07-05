package shared.variable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
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
    protected Map<String, Variable> parameters = new LinkedHashMap<>();
    protected List<Variable> indexedParameters = new ArrayList<>();
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
        this.parameters.put(var.getName(), var);
        this.indexedParameters.add(var);
    }

    public void addParameters(List<Variable> vars) {
        for (Variable v : vars) {
            this.addParameter(v);
        }
    }

    public void addParameters(Set<Variable> vars) {
        for (Variable v : vars) {
            this.addParameter(v);
        }
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
        if (this.types.isEmpty()) {
            this.types.addAll(returnStatement.getOutputVariables().get(0).getTypes());
        }
        this.returnStatement = returnStatement;
    }

    public String getName() {
        return this.name;
    }

    public Set<ChemTypes> getTypes() {
        return this.types;
    }

    public Map<String, Variable> getParameters() {
        return this.parameters;
    }

    public List<Variable> getIndexedParameters() {
        return this.indexedParameters;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("==========================").append(Statement.NL);
        sb.append(this.name).append(" Return type(s): ").append(this.types).append(Statement.NL);
        sb.append("\tParameters: ").append(this.parameters).append(Statement.NL);
        sb.append("==========================").append(Statement.NL);

        return sb.toString();
    }

    public List<Statement> getStatements() {
        return this.statements;
    }

    public void setStatements(Statement statement) {
        this.statements.add(statement);
    }
}
