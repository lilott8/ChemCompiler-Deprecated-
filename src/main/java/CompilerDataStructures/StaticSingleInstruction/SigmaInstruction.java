package CompilerDataStructures.StaticSingleInstruction;

import CompilerDataStructures.InstructionNode;

import java.util.ArrayList;

/**
 * Created by chriscurtis on 4/12/17.
 */
public class SigmaInstruction extends InstructionNode {

    private String __oringinalSymbol;


    public SigmaInstruction(String symbol, Integer successors){
        super(-1,null);
        __oringinalSymbol = symbol;
        this.__inputSymbols.add(symbol);
        while(successors-- >0)
            this.__outputSymbols.add(symbol);
    }


    public String toString(){
        return this.toString("");
    }
    public String toString(String indentBuffer){
        String ret = indentBuffer;

        for(String s: this.getOutputSymbols()){
            ret += s + " ";
        }

        ret+= "= SIGMA( " + this.getInputSymbols().get(0) + ")";
        return ret;
    }
}
