package ir;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * @created: 3/14/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class StatementBlock {

    private String scope;
    private Map<Integer, Statement> statements = new LinkedHashMap<>();

    public StatementBlock(String scope) {
        this.scope = scope;
    }

    public void addStatement(Statement s) {
        this.statements.put(s.getId(), s);
    }

    public void addStatements(List<Statement> statements) {
        for (Statement s : statements) {
            this.statements.put(s.getId(), s);
        }
    }

    public Map<Integer, Statement> getStatementMap() {
        return this.statements;
    }

    public List<Statement> getStatements() {
        return (List) this.statements.values();
    }

    public void clear() {
        this.statements.clear();
    }

    public String getScope() {
        return this.scope;
    }
}
