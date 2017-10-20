package compilation.datastructures.ssi;

import compilation.datastructures.node.InstructionNode;

/**
 * Created by chriscurtis on 4/12/17.
 */
public class SigmaInstruction extends InstructionNode {

    private String originalSymbol;

    public SigmaInstruction(String symbol, Integer successors){
        super(-1,null);
        originalSymbol = symbol;
        this.inputSymbols.add(symbol);
        while(successors-- >0)
            this.outputSymbols.add(symbol);
    }


    public String toString(){
        return this.toString("");
    }
    public String toString(String indentBuffer){
        String ret = indentBuffer;

        for(String s: this.getOutputSymbols()){
            ret += s + " ";
        }

        ret+= "= SIGMA( " + this.getInputSymbols().get(0) + ")" + originalSymbol;
        return ret;
    }
}
