package ir.graph;

import org.jgrapht.graph.DefaultEdge;

/**
 * @created: 3/9/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Edge extends DefaultEdge {

    public final TYPE purpose;

    public Edge(TYPE purpose) {
        super();
        this.purpose = purpose;
    }

    public Edge() {
        super();
        this.purpose = TYPE.FALLTHROUGH;
    }

    @Override
    public Object getSource() {
        return super.getSource();
    }

    @Override
    public Object getTarget() {
        return super.getTarget();
    }

    public String toString() {
        return super.toString() + this.purpose;
    }

    public enum TYPE {
        FALLTHROUGH, TRUE, FALSE
    }
}
