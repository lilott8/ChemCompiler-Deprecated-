package ControlFlowGraph;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class InstructionEdge {
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
}
