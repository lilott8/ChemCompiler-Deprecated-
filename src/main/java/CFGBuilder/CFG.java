package CFGBuilder;


import DataFlow.ReachingDefinitions;
import DominatorTree.DominatorTree;
import SymbolTable.NestedSymbolTable;
import executable.instructions.Instruction;
import variable.Variable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class CFG {
    private ArrayList<BasicBlock> __basicBlocks;
    private ArrayList<BasicBlockEdge> __edges;
    private NestedSymbolTable __symbolTable;
    private HashMap<String, List<Integer> > __instructionDefinintionTable;
    private HashMap<String, List<Integer> > __useTable;
    private List<InstructionNode> __instructions;
    private Integer __ID;
    private DominatorTree __dominatorTree;



    public CFG(){
        __basicBlocks = new ArrayList<BasicBlock>();
        __edges = new ArrayList<BasicBlockEdge>();
        __symbolTable = new NestedSymbolTable();
        __instructionDefinintionTable = new HashMap<String, List<Integer>>();
        __useTable = new HashMap<String, List<Integer>>();
        __instructions = new ArrayList<InstructionNode>();
        __ID = 0;

        __dominatorTree = null;

    }
    public CFG(Integer id){
        __basicBlocks = new ArrayList<BasicBlock>();
        __edges = new ArrayList<BasicBlockEdge>();
        __symbolTable = new NestedSymbolTable();
        __instructionDefinintionTable = new HashMap<String, List<Integer>>();
        __useTable = new HashMap<String, List<Integer>>();
        __instructions = new ArrayList<InstructionNode>();
        __ID = id;

        __dominatorTree = null;

    }
    public CFG(Integer id, NestedSymbolTable table){
        __basicBlocks = new ArrayList<BasicBlock>();
        __edges = new ArrayList<BasicBlockEdge>();
        __symbolTable = table;
        __instructionDefinintionTable = new HashMap<String, List<Integer>>();
        __useTable = new HashMap<String, List<Integer>>();
        __instructions = new ArrayList<InstructionNode>();
        __ID = id;

        __dominatorTree = null;

    }




    public Integer getNewID() { return __ID++;}
    private void AddBasicBlock(BasicBlock block) {
        __basicBlocks.add(block);
    }

    public BasicBlock newBasicBlock() {
        BasicBlock ret = new BasicBlock(__ID++);
        this.AddBasicBlock(ret);

        return ret;
    }
/*    public BasicBlock newBasicBlock() {
        return this.newBasicBlock(this.__symbolTable);
    }
*/

    public void insertInstructionNode(BasicBlock bb, Instruction instruction, Boolean isLeader) {
        InstructionNode node = new InstructionNode(__ID++,instruction,isLeader);
        bb.addInstruction(node);
    }
    public void insertInstructionNode(BasicBlock bb, Instruction instruction) {

    }


    public void addDominatorTree(DominatorTree t) {
        this.__dominatorTree = t;
    }
    public void addEdge(BasicBlock source, BasicBlock destination) {
        this.addEdge(source,destination,"UNCONDITIONAL");
    }

    public void addEdge(BasicBlock source, BasicBlock destination, String condition) {
        __edges.add(new BasicBlockEdge(source.ID(),destination.ID(), condition));
    }

    public void addInstruction(InstructionNode node) {
        __instructions.add(node);
    }
    public void addDefinition(String key, Integer opID) {
        List<Integer> opIDs;
        if (__instructionDefinintionTable.containsKey(key)) {
            opIDs = __instructionDefinintionTable.get(key);
        }
        else {
            opIDs = new ArrayList<Integer>();
        }
        opIDs.add(opID);

        __instructionDefinintionTable.put(key,opIDs);
    }
    public void addDefinition(String key) {
        this.addDefinition(key,0);
    }

    public void addUse(String key, Integer opID) {
        List<Integer> opIDs;
        if (__useTable.containsKey(key)) {
            opIDs = __useTable.get(key);
        }
        else {
            opIDs = new ArrayList<Integer>();
        }
        opIDs.add(opID);

        __useTable.put(key,opIDs);
    }

    public NestedSymbolTable getSymbolTable() { return __symbolTable; }
    public void setSymbolTable(NestedSymbolTable table) { __symbolTable = table; }

    public HashMap<String, List<Integer> > getDefintionTable() { return __instructionDefinintionTable; }
    public HashMap<String, List<Integer> > getUseTable() { return  __useTable; }
    public List<InstructionNode> getInstructions() { return __instructions; }
    public List<BasicBlock> getBasicBlocks() { return __basicBlocks; }
    public List<BasicBlockEdge> getBasicBlockEdges() { return __edges; }



    public void renameVariables() {
        for(BasicBlock bb : __basicBlocks){
            for(InstructionNode node: bb.getInstructions()) {

                List<String> keySet = new ArrayList<String>();
                for(String key : node.Instruction().getOutputs().keySet())
                    keySet.add(key);

                for (String key : keySet ) {
                    String newName = this.__symbolTable.getUniqueVariableName();
                    Variable original =  node.Instruction().getOutputs().get(key);

                    node.Instruction().removeOutput(original);
                    original.setID(newName);
                    original.setName(newName);

                    node.Instruction().addOutput(original);
                    this.__symbolTable.addRenamedVariable(key,newName);
                }
            }
        }
    }

    public String toString(){
        return this.toString("");
    }

    public String toString(String indentBuffer){
        String ret = indentBuffer + "CFG: \n";
        for(BasicBlock bb: this.__basicBlocks) {
            ret += bb.toString(indentBuffer+'\t') + '\n';
        }
        ret +=indentBuffer + "CFG Edges: \n";
        for(BasicBlockEdge edge: __edges) {
            ret += edge.toString(indentBuffer+'\t') + '\n';
        }

        ret+="\n SYMBOL TABLE\n";
        ret+=__symbolTable.toString();
        return ret;
    }


    public void ConvertToSSA(){
        this.__dominatorTree = new DominatorTree(this);


    }

    public String UseTableToString() {
        String ret = "";
        for(String key : __useTable.keySet()) {
            ret += key + ": ";
            for (Integer use : __useTable.get(key)) {
                ret += use + " ";
            }
            ret += '\n';
        }
        return ret;
    }

    public String DefTableToString() {
        String ret = "";
        for(String key : __instructionDefinintionTable.keySet()) {
            ret += key + ": ";
            for (Integer use : __instructionDefinintionTable.get(key)) {
                ret += use + " ";
            }
            ret += '\n';
        }
        return ret;
    }
}