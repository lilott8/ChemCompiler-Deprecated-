package compilation.datastructures;

import org.jgrapht.graph.DefaultEdge;

import java.io.Serializable;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class InstructionEdge extends DefaultEdge implements Serializable {
    private Integer id;
    private Integer source;
    private Integer destination;

    public InstructionEdge(Integer source, Integer destination) {
        this.source = source;
        this.destination = destination;
        id = source*destination;
    }

    public String toString() {
        return this.toString("");
    }
    public String toString(String indentBuffer) {
        return indentBuffer + source.toString() + "->" + destination;
    }

    public Integer getSource() { return source; }
    public Integer getDestination() { return destination; }
    public Integer getId() {
        return id;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (!(obj instanceof InstructionEdge))
            return false;
        InstructionEdge other = (InstructionEdge) obj;
        if (source.equals(other.source)) {
            return destination.equals(other.destination);
        }
        return false;
    }
}
