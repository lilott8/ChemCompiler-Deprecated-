package ControlFlowGraph;

//import ChemicalInteractions.ChemicalInteraction;
import com.sun.org.apache.xpath.internal.operations.Bool;
import executable.instructions.Instruction;

import java.io.Serializable;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class InstructionNode implements Serializable {
    private Integer __ID;
    private Instruction __instruction;
    private Set<String> __dispenseSymbols;

    //private ChemicalInteraction __interaction;
    private Boolean __leader;

    public InstructionNode(Integer id, Instruction instruction) {
        __dispenseSymbols = new HashSet<String>();
        __ID = id;
        __instruction = instruction;
      //  __interaction = null;
        __leader = false;
    }
    public InstructionNode(Integer id, Instruction instruction, Boolean isLeader) {
        __dispenseSymbols = new HashSet<String>();
        __ID = id;
        __instruction = instruction;
      //  __interaction = null;
        __leader = isLeader;
    }

    public Integer ID() {
        return __ID;
    }

    public Instruction Instruction() {
        return __instruction;
    }
   // public ChemicalInteraction getChemicalInteraction() {return __interaction; }

 //   public void addChemicalInteraction(ChemicalInteraction ci) { __interaction = ci; }
    public void setLeader(Boolean isleader) { __leader = isleader; }

    public Boolean isLeader() { return __leader; }
    public void addImplicitDispense(String symbol) {
        this.__dispenseSymbols.add(symbol);
    }

    public Set<String> getDispenseSymbols(){ return __dispenseSymbols; }
    public String toString() {
        return this.toString("");
    }
    public String toString(String indentBuffer) {
        String ret = indentBuffer + __ID.toString() + ":\t";
        for(String out: __instruction.getOutputs().keySet())
            ret += out + " = ";

        ret +=  __instruction.getName() + " ";

        for(String input : __instruction.getInputs().keySet())
            ret+=  "\"" + input + "\" ";


        return  ret;
    }

}
