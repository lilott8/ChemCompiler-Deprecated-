package Phases.Inference;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Constraint<T> {

    // Todo: Abstract this better.
    private T term;
    private String type;

    public Constraint(T term, String type) {
        this.term = term;
        this.type = type;
    }

    public T getTerm() {
        return term;
    }

    public String getType() {
        return type;
    }
}
