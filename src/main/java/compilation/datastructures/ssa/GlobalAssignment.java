package compilation.datastructures.ssa;

import compilation.datastructures.InstructionNode;

/**
 * Created by chriscurtis on 3/7/17.
 */
public class GlobalAssignment extends InstructionNode {
    //String __symbol;

    public GlobalAssignment(String symbol){
        super(-1,null);
        this.__outputSymbols.add(symbol);
        //this.__symbol = symbol;
    }

    public String toString(){
        return this.toString("");
    }

    public String toString(String indentBuffer) {
        //return super.toString(indentBuffer);
        String ret = "";

        for(String symbol : this.__outputSymbols)
            ret +=  indentBuffer + "Define: " + symbol;

       return ret;
    }

  //  public String getSymbol() {return  this.__symbol; }
   // public void setSymbol(String symbol) {this.__symbol = symbol; }
}