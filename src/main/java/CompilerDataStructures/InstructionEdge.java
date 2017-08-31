package CompilerDataStructures;

import java.io.Serializable;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class InstructionEdge implements Serializable {
    private Integer __source;
    private Integer __destination;

    public InstructionEdge(Integer source, Integer destination) {
        __source = source;
        __destination = destination;
    }

    public String toString() {
        return this.toString("");
    }
    public String toString(String indentBuffer) {
        return indentBuffer + __source.toString() + "->" + __destination;
    }

    public Integer getSource() { return __source; }
    public Integer getDestination() { return __destination; }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (!(obj instanceof InstructionEdge))
            return false;
        InstructionEdge other = (InstructionEdge) obj;
        if (__source.equals(other.__source)) {
            return __destination.equals(other.__destination);
        }
        return false;
    }
}
