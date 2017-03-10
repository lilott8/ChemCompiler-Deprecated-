package StaticSingleInstruction;

//import ChemicalInteractions.ChemicalInteraction;
import executable.instructions.Instruction;
import substance.Property;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class InstructionNode implements Serializable {
    private Integer __ID;
    private Instruction __instruction;
    private Set<String> __dispenseSymbols;
    protected ArrayList<String> __inputSymbols;
    protected ArrayList<String> __outputSymbols;


    private Boolean __leader;

    public InstructionNode(Integer id, Instruction instruction) {
        __dispenseSymbols = new HashSet<String>();
        __inputSymbols = new ArrayList<String>();
        __outputSymbols = new ArrayList<String>();

        __ID = id;
        __instruction = instruction;

        __leader = false;

        StripInputsAndOutputs(instruction);
    }
    public InstructionNode(Integer id, Instruction instruction, Boolean isLeader ) {
        __dispenseSymbols = new HashSet<String>();
        __inputSymbols = new ArrayList<String>();
        __outputSymbols = new ArrayList<String>();

        __ID = id;
        __instruction = instruction;

        __leader = isLeader;
        StripInputsAndOutputs(instruction);
    }

    public Integer ID() {
        return __ID;
    }

    public Instruction Instruction() {
        return __instruction;
    }
    //public ChemicalInteraction getChemicalInteraction() {return __interaction; }

    //public void addChemicalInteraction(ChemicalInteraction ci) { __interaction = ci; }
    public void setLeader(Boolean isleader) { __leader = isleader; }

    public Boolean isLeader() { return __leader; }
    public void addImplicitDispense(String symbol) {
        this.__dispenseSymbols.add(symbol);
    }

    public ArrayList<String> getInputSymbols() { return __inputSymbols; }
    public ArrayList<String> getOutputSymbols() { return __outputSymbols; }
    public Set<String> getDispenseSymbols(){ return __dispenseSymbols; }
    public String toString() {
        return this.toString("");
    }
    public String toString(String indentBuffer) {
        String ret = indentBuffer ;// + __ID.toString() + ":\t";
        for(String out: __outputSymbols)
            ret += out + " = ";

        if(__instruction != null)
            ret +=  __instruction.getName() + " ";

        for(String input : __inputSymbols)
            ret+=  " \"" + input + "\"";

        if(__instruction != null)
            for(Property property : __instruction.getProperties())
                ret += ", " + property.toString();

        return  ret;
    }


    private void StripInputsAndOutputs(Instruction instruction){
        if(instruction == null)
            return;

        for(String inputSymbol : instruction.getInputs().keySet()){
            __inputSymbols.add(inputSymbol);
        }

        for(String outputSymbol : instruction.getOutputs().keySet()){
            __outputSymbols.add(outputSymbol);
        }
    }

}
