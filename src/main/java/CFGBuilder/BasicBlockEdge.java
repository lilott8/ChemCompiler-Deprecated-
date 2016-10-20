package CFGBuilder;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class BasicBlockEdge {
    private Integer __source;
    private Integer __destination;

//this still needs to be created.
    private String __condition;

    public BasicBlockEdge(Integer source, Integer destination) {
        __source = source;
        __destination = destination;
        __condition = "UNCONDITIONAL";
    }

    public BasicBlockEdge(Integer source, Integer destination, String condition) {
        __source = source;
        __destination = destination;
        __condition = condition;
    }

    public String toString() {
        return this.toString("");
    }
    public String toString(String indentBuffer) {
        return indentBuffer + __source.toString() + " ->" + __destination + " : " + __condition;
    }

    public Integer getSource() { return __source; }
    public Integer getDestination() {return __destination; }

}
