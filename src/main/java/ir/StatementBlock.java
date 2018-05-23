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

    /**
     * Returns a string representation of the object. In general, the
     * {@code toString} method returns a string that
     * "textually represents" this object. The result should
     * be a concise but informative representation that is easy for a
     * person to read.
     * It is recommended that all subclasses override this method.
     * <p>
     * The {@code toString} method for class {@code Object}
     * returns a string consisting of the name of the class of which the
     * object is an instance, the at-sign character `{@code @}', and
     * the unsigned hexadecimal representation of the hash code of the
     * object. In other words, this method returns a string equal to the
     * value of:
     * <blockquote>
     * <pre>
     * getClass().getName() + '@' + Integer.toHexString(hashCode())
     * </pre></blockquote>
     *
     * @return a string representation of the object.
     */
    @Override
    public String toString() {
        return scope + ":\t" + statements;
    }
}
