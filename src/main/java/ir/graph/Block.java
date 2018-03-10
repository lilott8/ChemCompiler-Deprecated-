package ir.graph;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import ir.statements.Statement;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Block {
    private List<Statement> statements = new ArrayList<>();

    private static int idCounter = 0;
    private int id = idCounter++;

    public Block(Statement... statements) {
        this.statements.addAll(Arrays.asList(statements));
    }

    public Block() {
    }

    public Statement getLeader() {
        return this.statements.get(0);
    }

    public Statement getLastStatement() {
        return this.statements.get(this.statements.size()-1);
    }

    public int getId() {
        return this.id;
    }

    public List<Statement> getStatements() {
        return statements;
    }

    public void setStatements(List<Statement> statements) {
        this.statements.addAll(statements);
    }

    public void addStatement(Statement statement) {
        this.statements.add(statement);
    }
}
