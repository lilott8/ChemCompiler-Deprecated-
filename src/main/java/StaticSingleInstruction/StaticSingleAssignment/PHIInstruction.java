package StaticSingleInstruction.StaticSingleAssignment;

import StaticSingleInstruction.InstructionNode;

import java.util.ArrayList;

public class PHIInstruction extends  InstructionNode{

    protected String __outputSymbol;
    protected ArrayList<String> __joinedSymbols;

    public PHIInstruction(){
        super(-1,null);
        this.__outputSymbol = "";
        this.__joinedSymbols = new ArrayList<String>();

    }
    public PHIInstruction(String symbol){
        super(-1,null);
        this.__outputSymbol = symbol;
        this.__joinedSymbols = new ArrayList<String>();
    }
    public String toString(){
        return this.toString("");
    }

    public String toString(String indentBuffer) {
        String ret =  indentBuffer + "PHI(" + this.__outputSymbol+ "):";
        for(String joined : __joinedSymbols){
            ret+= joined;
        }
        return ret;
    }
}