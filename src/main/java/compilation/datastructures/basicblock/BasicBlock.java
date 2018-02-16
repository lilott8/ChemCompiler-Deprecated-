package compilation.datastructures.basicblock;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import compilation.datastructures.InstructionEdge;
import compilation.datastructures.node.InstructionNode;
import compilation.datastructures.ssa.GlobalAssignment;
import compilation.datastructures.ssa.PHIInstruction;
import compilation.symboltable.NestedSymbolTable;
import executable.instructions.Combine;
import executable.instructions.Instruction;
import executable.instructions.Output;
import executable.instructions.Split;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class BasicBlock implements Serializable {
    private Map<String, Set<Integer>> basicBlockEntry = new HashMap<>();
    private Map<String, Set<Integer>> basicBlockExit = new HashMap<>();
    private Set<String> definitions = new HashSet<>();
    private Set<String> killedSet = new HashSet<>();

    private NestedSymbolTable symbolTable;
    public static final String NL = System.lineSeparator();

    private List<InstructionNode> instructions = new ArrayList<>();
    private List<InstructionEdge> edges = new ArrayList<>();
    private Integer id;

    public BasicBlock(Integer id, NestedSymbolTable table) {
        symbolTable = table;
        this.id = id;
    }

    //copy constructor
    public BasicBlock(BasicBlock bb) {
        basicBlockEntry = bb.basicBlockEntry;
        basicBlockExit = bb.basicBlockExit;
        symbolTable = bb.symbolTable;
        killedSet = bb.killedSet;
        definitions = bb.definitions;
        instructions = bb.instructions;
        edges = bb.edges;
        id = bb.id;
    }

    public void addVariableDefinition(Instruction i){
       if (!i.getOutputs().isEmpty()) {
           this.definitions.addAll(i.getOutputs().keySet());
       }
    }

    public Set<String> getDefinitions() {
        return this.definitions;
    }

    public Set<String> getKilledSet() {
        return this.killedSet;
    }


    public Boolean containsInstruction(int index) {
        boolean retVal = false;
        for (InstructionNode instr : instructions) {
            if (instr.getId() == index) {
                retVal = true;
            }
        }
        return retVal;
    }


    public Boolean processPredecessors(List<BasicBlock> predecessors) {
        Boolean changed = false;
        for (BasicBlock bb : predecessors) {
            for (String outgoingSymbol : bb.basicBlockExit.keySet()) {
                if (!this.basicBlockEntry.containsKey(outgoingSymbol)) {
                    //if the symbol does not exist yet add entire set from predecessor
                    changed = true;
                    Set<Integer> copySet = new HashSet<Integer>();
                    copySet.addAll(bb.basicBlockExit.get(outgoingSymbol));
                    this.basicBlockEntry.put(outgoingSymbol, copySet);
                } else {
                    Set<Integer> UsageIDs = bb.basicBlockExit.get(outgoingSymbol);
                    for (Integer usageID : UsageIDs) {
                        if (!this.basicBlockEntry.get(outgoingSymbol).contains(usageID)) {
                            changed = true;
                            this.basicBlockEntry.get(outgoingSymbol).add(usageID);
                        }
                    }
                }
            }
        }

        //Get the Definitions from Parent
        NestedSymbolTable ancestorDefinitions = symbolTable.getParent();
        while (ancestorDefinitions != null) {
            for (String key : ancestorDefinitions.getDefinitionTable().keySet()) {
                if (!this.basicBlockEntry.containsKey(key)) {
                    //if the symbol does not exist yet add entire set from predecessor
                    //changed = true;
                    Set<Integer> anscesotorSet = new HashSet<Integer>();
                    anscesotorSet.add(-2);
                    this.basicBlockEntry.put(key, anscesotorSet);
                }
            }
            ancestorDefinitions = ancestorDefinitions.getParent();
        }

        return changed;
    }

    public Boolean processOutput() {
        Boolean changed = false;
        for (String symbol : this.symbolTable.getUsagedTable().keySet()) {
            if(this.getSymbolTable().contains(symbol) && this.getSymbolTable().get(symbol).IsStationary())
                continue;
            Integer lastUsed = this.symbolTable.lastUsedIn(symbol);
            if (lastUsed != -1 && (!this.basicBlockExit.containsKey(symbol))) {
                changed = true;
                Set<Integer> usageSet = new HashSet<Integer>();
                usageSet.add(lastUsed);
                this.basicBlockExit.put(symbol, usageSet);
            }
        }
        for (String definedSymbol : this.symbolTable.getDefinitionTable().keySet()) {
            if(this.getSymbolTable().contains(definedSymbol) && this.getSymbolTable().get(definedSymbol).IsStationary())
                continue;
            if(this.symbolTable.getUsagedTable().containsKey(definedSymbol) && this.getSymbolTable().getUsagedTable().get(definedSymbol)==-1)
                continue;
            if (!this.basicBlockExit.containsKey(definedSymbol)) {
                changed = true;
                Set<Integer> usageSet = new HashSet<Integer>();
                usageSet.add(this.symbolTable.getDefinitionID(definedSymbol));
                this.basicBlockExit.put(definedSymbol, usageSet);
            }
        }
        for (String entrySymbol : this.basicBlockEntry.keySet()) {
            if (!this.symbolTable.getUsagedTable().containsKey(entrySymbol)) { // if I havent used the declaration in basic block
                if ((!this.basicBlockEntry.get(entrySymbol).contains(-2))) { // if symbol isnt a global declaration
                    if ((!this.basicBlockExit.containsKey(entrySymbol)) || this.basicBlockExit.get(entrySymbol).size() != this.basicBlockEntry.get(entrySymbol).size()) {
                        changed = true;
                        this.basicBlockExit.put(entrySymbol, this.basicBlockEntry.get(entrySymbol));
                    }
                }
            }
        }
        return changed;
    }

    public void updateUsage(String symbol , InstructionNode node) {
        if (node.getInstruction() instanceof Combine ||
                node.getInstruction() instanceof Output ||
                node.getInstruction() instanceof Split) {
            if(this.symbolTable.contains(symbol) && this.symbolTable.get(symbol).IsStationary())
                this.symbolTable.updateLastUsedIn(symbol, node.getId());
            else
                this.symbolTable.updateLastUsedIn(symbol, -1);
        }
        else {
            this.symbolTable.updateLastUsedIn(symbol, node.getId());
        }
    }


    public void addInstruction(InstructionNode instruction) {
        if(instruction instanceof PHIInstruction)
            instructions.add(0, instruction);
        else if (instruction instanceof GlobalAssignment) {
            instructions.add(instruction);
            this.definitions.addAll(instruction.getInputSymbols());
        }
        else
            instructions.add(instruction);
    }
    public void addInstruction(int index, InstructionNode instruction) {
        instructions.add(index, instruction);
    }

    public void addEdge(InstructionNode source, InstructionNode destination) {
        this.addEdge(source.getId(),destination.getId());
    }
    public void addEdge(Integer source, Integer destination) {
        edges.add(new InstructionEdge(source,destination));
    }

    public NestedSymbolTable getSymbolTable() { return symbolTable; }
    public List<InstructionNode> getInstructions() { return instructions; }
    public List<InstructionEdge> getEdges() {return edges; }
    public Boolean hasIncomingSymbol(String symbol) {return this.basicBlockEntry.containsKey(symbol); }
    public Set<Integer> getBasicBlockEntryUsage(String symbol) { return this.basicBlockEntry.get(symbol); }
    public Map<String, Set<Integer>> getBasicBlockEntryTable() { return this.basicBlockEntry; }
    public Map<String, Set<Integer>> getBasicBlockExitTable() { return this.basicBlockExit; }

    public Integer getId() {
        return id;
    }


    public String metaToString(){
        String ret = "";
        ret += this.toString();

        ret+="In:"+'\n';
        for(String symbol: this.basicBlockEntry.keySet()) {
            ret += '\t' + symbol + ": ";
            for(Integer usage: this.basicBlockEntry.get(symbol)){
                ret += usage + " ";
            }
            ret += '\n';
        }

        ret += "Out: " + '\n';
        for(String symbol: this.basicBlockExit.keySet()){
            ret += '\t' + symbol + ": ";
            for(Integer usage: this.basicBlockExit.get(symbol)) {
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
        StringBuffer sb = new StringBuffer();
        sb.append(indentBuffer).append("Basic Block: ").append(id).append(NL);
        sb.append(indentBuffer).append("\t Formula Visibility: ").append(NL);
        for (InstructionNode node : instructions) {
            sb.append(node.toString(indentBuffer + "\t\t")).append(NL);
        }
        sb.append(indentBuffer).append("\t Edges: ").append(NL);
        for (InstructionEdge edge : edges) {
            sb.append(edge.toString(indentBuffer + "\t\t")).append(NL);
        }
        sb.append(indentBuffer).append("\t Definitions: ").append(NL);
        for (String definition : this.definitions) {
            sb.append(indentBuffer).append("\t\t").append(definition).append(NL);
        }
        sb.append(indentBuffer).append("\t Killed Set: ").append(NL);
        for (String killed : this.killedSet) {
            sb.append(indentBuffer).append("\t\t").append(killed).append(NL);
        }
        /*for(String definition: symbolTable.getDefinitionTable().keySet()){
            ret +=indentBuffer + "\t\t" + symbolTable.get(definition) + '\n';
        }*/
        return sb.toString();
    }
}