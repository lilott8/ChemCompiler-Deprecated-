package StaticSingleInstruction.BasicBlock;

import StaticSingleInstruction.InstructionEdge;
import StaticSingleInstruction.InstructionNode;
import StaticSingleInstruction.StaticSingleAssignment.PHIInstruction;
import StaticSingleInstruction.StaticSingleAssignment.GlobalAssignment;
import SymbolTable.NestedSymbolTable;
import executable.instructions.Combine;
import executable.instructions.Instruction;
import executable.instructions.Output;
import executable.instructions.Split;

import java.io.Serializable;
import java.util.*;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class BasicBlock implements Serializable {
    private HashMap<String, Set<Integer>> __basicBlockEntry;
    private HashMap<String, Set<Integer>> __basicBlockExit;
    private HashSet<String> __definitions;
    private HashSet<String> __killedSet;

    private NestedSymbolTable __symbolTable;


    private ArrayList<InstructionNode> __instructions;
    private ArrayList<InstructionEdge> __edges;
    private Integer __ID;

    public BasicBlock(Integer id, NestedSymbolTable table) {
        __basicBlockEntry = new HashMap<String, Set<Integer>>();
        __basicBlockExit = new HashMap<String, Set<Integer>>();
        __symbolTable = table;
        __definitions = new HashSet<String>();
        __killedSet = new HashSet<String>();

        __instructions = new ArrayList<InstructionNode>();
        __edges = new ArrayList<InstructionEdge>();
        __ID = id;
    }

    public BasicBlock(BasicBlock bb) {
        __killedSet = new HashSet<String>();
        __definitions = new HashSet<String>();

        __instructions = bb.getInstructions();
        __edges = bb.getEdges();
        __ID = bb.ID();
    }


    public void AddVariableDefinition(Instruction i){
       if (! i.getOutputs().isEmpty()){
           for(String definition : i.getOutputs().keySet())
               this.__definitions.add(definition);
       }
    }

    public HashSet<String> getDefinitions() { return this.__definitions; }
    public HashSet<String> getKilledSet() { return this.__killedSet; }




    public Boolean processPredecessors(List<BasicBlock> predecessors) {
        Boolean changed = false;
        for (BasicBlock bb : predecessors) {
            for (String outgoingSymbol : bb.__basicBlockExit.keySet()) {
                if (!this.__basicBlockEntry.containsKey(outgoingSymbol)) {
                    //if the symbol does not exist yet add entire set from predecessor
                    changed = true;
                    Set<Integer> copySet = new HashSet<Integer>();
                    for(Integer id: bb.__basicBlockExit.get(outgoingSymbol)){
                        copySet.add(id);
                    }

                    this.__basicBlockEntry.put(outgoingSymbol, copySet);
                } else {
                    Set<Integer> UsageIDs = bb.__basicBlockExit.get(outgoingSymbol);
                    for (Integer usageID : UsageIDs) {
                        if (!this.__basicBlockEntry.get(outgoingSymbol).contains(usageID)) {
                            changed = true;
                            this.__basicBlockEntry.get(outgoingSymbol).add(usageID);
                        }
                    }
                }
            }
        }

        //Get the Definitions from Parent
        NestedSymbolTable ancestorDefinitions = __symbolTable.getParent();
        while (ancestorDefinitions != null) {
            for (String key : ancestorDefinitions.getDefinitionTable().keySet()) {
                if (!this.__basicBlockEntry.containsKey(key)) {
                    //if the symbol does not exist yet add entire set from predecessor
                    //changed = true;
                    Set<Integer> anscesotorSet = new HashSet<Integer>();
                    anscesotorSet.add(-2);
                    this.__basicBlockEntry.put(key, anscesotorSet);
                }
            }
            ancestorDefinitions = ancestorDefinitions.getParent();
        }

        return changed;
    }

    public Boolean processOutput() {
        Boolean changed = false;
        for (String symbol : this.__symbolTable.getUsagedTable().keySet()) {
            if(this.getSymbolTable().contains(symbol) && this.getSymbolTable().get(symbol).IsStationary())
                continue;
            Integer lastUsed = this.__symbolTable.lastUsedIn(symbol);
            if (lastUsed != -1 && (!this.__basicBlockExit.containsKey(symbol))) {
                changed = true;
                Set<Integer> usageSet = new HashSet<Integer>();
                usageSet.add(lastUsed);
                this.__basicBlockExit.put(symbol, usageSet);
            }
        }
        for (String definedSymbol : this.__symbolTable.getDefinitionTable().keySet()) {
            if(this.getSymbolTable().contains(definedSymbol) && this.getSymbolTable().get(definedSymbol).IsStationary())
                continue;
            if(this.__symbolTable.getUsagedTable().containsKey(definedSymbol) && this.getSymbolTable().getUsagedTable().get(definedSymbol)==-1)
                continue;
            if (!this.__basicBlockExit.containsKey(definedSymbol)) {
                changed = true;
                Set<Integer> usageSet = new HashSet<Integer>();
                usageSet.add(this.__symbolTable.getDefinitionID(definedSymbol));
                this.__basicBlockExit.put(definedSymbol, usageSet);
            }
        }
        for (String entrySymbol : this.__basicBlockEntry.keySet()) {
            if (!this.__symbolTable.getUsagedTable().containsKey(entrySymbol)) { // if I havent used the declaration in basic block
                if ((!this.__basicBlockEntry.get(entrySymbol).contains(-2))) { // if symbol isnt a global declaration
                    if ((!this.__basicBlockExit.containsKey(entrySymbol)) || this.__basicBlockExit.get(entrySymbol).size() != this.__basicBlockEntry.get(entrySymbol).size()) {
                        changed = true;
                        this.__basicBlockExit.put(entrySymbol, this.__basicBlockEntry.get(entrySymbol));
                    }
                }
            }
        }
        return changed;
    }

    public void updateUsage(String symbol , InstructionNode node) {
        if (node.Instruction() instanceof Combine ||
                node.Instruction() instanceof Output ||
                node.Instruction() instanceof Split) {
            if(this.__symbolTable.contains(symbol) && this.__symbolTable.get(symbol).IsStationary())
                this.__symbolTable.updateLastUsedIn(symbol, node.ID());
            else
                this.__symbolTable.updateLastUsedIn(symbol, -1);
        }
        else {
            this.__symbolTable.updateLastUsedIn(symbol, node.ID());
        }
    }


    public void addInstruction(InstructionNode instruction) {
        if(instruction instanceof PHIInstruction)
            __instructions.add(0, instruction);
        else if (instruction instanceof GlobalAssignment) {
            __instructions.add(instruction);
            for(String symbol :instruction.getInputSymbols())
                this.__definitions.add(symbol);
        }
        else
            __instructions.add(instruction);
    }
    public void addInstruction(int index, InstructionNode instruction) {
        __instructions.add(index, instruction);
    }

    public void addEdge(InstructionNode source, InstructionNode destination) {
        this.addEdge(source.ID(),destination.ID());
    }
    public void addEdge(Integer source, Integer destination) {
        __edges.add(new InstructionEdge(source,destination));
    }

    public NestedSymbolTable getSymbolTable() { return __symbolTable; }
    public ArrayList<InstructionNode> getInstructions() { return __instructions; }
    public ArrayList<InstructionEdge> getEdges() {return __edges; }
    public Boolean hasIncomingSymbol(String symbol) {return this.__basicBlockEntry.containsKey(symbol); }
    public Set<Integer> getBasicBlockEntryUsage(String symbol) { return this.__basicBlockEntry.get(symbol); }
    public Map<String, Set<Integer>> getBasicBlockEntryTable() { return this.__basicBlockEntry; }
    public Map<String, Set<Integer>> getBasicBlockExitTable() { return this.__basicBlockExit; }
    public Integer ID(){
        return __ID;
    }


    public String metaToString(){
        String ret = "";
        ret += this.toString();

        ret+="In:"+'\n';
        for(String symbol: this.__basicBlockEntry.keySet()) {
            ret += '\t' + symbol + ": ";
            for(Integer usage: this.__basicBlockEntry.get(symbol)){
                ret += usage + " ";
            }
            ret += '\n';
        }

        ret += "Out: " + '\n';
        for(String symbol: this.__basicBlockExit.keySet()){
            ret += '\t' + symbol + ": ";
            for(Integer usage: this.__basicBlockExit.get(symbol)) {
                ret += usage + " ";
            }
            ret += '\n';
        }
        ret += '\n';



        return ret;
    }

    public  String toString() {
        return this.toString("");
    }
    public  String toString(String indentBuffer) {
        String ret = indentBuffer + "Basic Block : " + __ID.toString() + '\n';

        ret += indentBuffer + '\t' + "Instructions: \n";
        for(InstructionNode node : __instructions)
            ret += node.toString(indentBuffer+'\t'+'\t') +'\n';
        ret += indentBuffer +'\t' + "Edges: \n";
        for(InstructionEdge edge : __edges)
            ret += edge.toString(indentBuffer+'\t'+'\t') + '\n';

        ret += indentBuffer + '\t' + "Definitions: "+'\n';
        for(String definition: this.__definitions){
            ret +=indentBuffer + "\t\t" + definition + '\n';
        }
        /*for(String definition: __symbolTable.getDefinitionTable().keySet()){
            ret +=indentBuffer + "\t\t" + __symbolTable.get(definition) + '\n';
        }*/
        return ret;
    }
}