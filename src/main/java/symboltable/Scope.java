package symboltable;

/**
 * @created: 2/7/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Scope {

    public static final String DEFAULT_SCOPE = "DEFAULT_SCOPE";

    private String scope = DEFAULT_SCOPE;
    private String name = DEFAULT_SCOPE;

    public Scope() {}

    public Scope(String name) {
        this.name = name;
    }

    public String getScope() {
        return this.name;
    }

    public String toString() {
        return getScope();
    }
}
