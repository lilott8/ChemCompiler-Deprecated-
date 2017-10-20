package compilation.datastructures.ssa;

import compilation.datastructures.node.InstructionNode;

/**
 * Created by chriscurtis on 3/7/17.
 */
public class GlobalAssignment extends InstructionNode {

    public GlobalAssignment(String symbol){
        super(-1,null);
        this.outputSymbols.add(symbol);
    }

    public String toString(){
        return this.toString("");
    }

    public String toString(String indentBuffer) {
        String ret = "";

        for(String symbol : this.outputSymbols)
            ret +=  indentBuffer + "Define: " + symbol;

       return ret;
    }
}
