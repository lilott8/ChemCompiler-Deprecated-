package CompilerDataStructures.StaticSingleAssignment;

import CompilerDataStructures.InstructionNode;

import java.util.ArrayList;

public class PHIInstruction extends  InstructionNode{

    private  String __oringinalSymbol;
   // protected String __outputSymbol;
    protected ArrayList<String> __joinedSymbols;


    public PHIInstruction(String symbol, Integer numJoined){
        super(-1,null);
        __oringinalSymbol = symbol;
        this.__outputSymbols.add(symbol);
       // this.__outputSymbol = symbol;
        this.__joinedSymbols = new ArrayList<String>();
        while(numJoined-- >0) {
            this.__joinedSymbols.add(symbol);
            this.__inputSymbols.add(symbol);
        }
    }

    public void InsertNodeAtIndex(Integer index, String symbol){
        while (index >= __joinedSymbols.size()) {
            __joinedSymbols.add("");
        }
        __joinedSymbols.set(index,symbol);
    }

    public String getOriginalName() { return this.__oringinalSymbol; }
   // public void setPHIName(String symbol) { this.__outputSymbol = symbol; }

    public String toString(){
        return this.toString("");
    }

    public String toString(String indentBuffer) {

        String ret = indentBuffer ;
        //this should only ever be one.
        for(String inputSymbol : this.getOutputSymbols())
            ret += inputSymbol;
        ret+= " = PHI(";
        for(String joined : __joinedSymbols){
            ret+= joined + " ";
        }
        ret+= ") ";
        return ret;
    }
}