package compilation.datastructures.ssa;

import java.util.ArrayList;

import compilation.datastructures.InstructionNode;

public class PHIInstruction extends  InstructionNode{

    private  String oringinalSymbol;
   // protected String __outputSymbol;
    protected ArrayList<String> joinedSymbols = new ArrayList<>();


    public PHIInstruction(String symbol, Integer numJoined){
        super(-1,null);
        oringinalSymbol = symbol;
        this.outputSymbols.add(symbol);
       // this.__outputSymbol = symbol;
        while(numJoined-- > 0) {
            this.joinedSymbols.add(symbol);
            this.inputSymbols.add(symbol);
        }
    }

    public void insertNodeAtIndex(Integer index, String symbol){
        while (index >= joinedSymbols.size()) {
            joinedSymbols.add("");
        }
        joinedSymbols.set(index,symbol);
    }

    public String getOriginalName() { return this.oringinalSymbol; }
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
        for(String joined : joinedSymbols){
            ret+= joined + " ";
        }
        ret+= ") ";
        return ret;
    }
}