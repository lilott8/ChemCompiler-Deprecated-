package ControlFlowGraph;


import ChemicalInteractions.ChemicalResolution;
import DominatorTree.DominatorTree;
import SymbolTable.NestedSymbolTable;
import executable.instructions.Instruction;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import substance.Chemical;
import substance.Substance;
import variable.Instance;
import variable.Variable;

import java.util.*;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class CFG {
    public static final Logger logger = LogManager.getLogger(CFG.class);



    private ArrayList<BasicBlock> __basicBlocks;
    private ArrayList<BasicBlockEdge> __edges;
    private HashMap< Integer, Set<Integer>> __basicBlockPredecessors;
    private HashMap< Integer, Set<Integer>> __basicBlockSuccessors;


    private NestedSymbolTable __symbolTable;
    private HashMap<String, List<Integer> > __instructionDefinintionTable;
   // private HashMap<String, List<Integer> > __useTable;
    private List<InstructionNode> __instructions;
    private Integer __UniqueIDs;
    private Integer __ID;
    private DominatorTree __dominatorTree;


    private void initializeData(){
        __basicBlocks = new ArrayList<BasicBlock>();
        __edges = new ArrayList<BasicBlockEdge>();
        __symbolTable = new NestedSymbolTable();
        //__instructionDefinintionTable = new HashMap<String, List<Integer>>();
        //__useTable = new HashMap<String, List<Integer>>();
        __instructions = new ArrayList<InstructionNode>();
        __ID = 0;
        __UniqueIDs = __ID++;

        __dominatorTree = null;
        __basicBlockPredecessors = new HashMap<Integer, Set<Integer>>();
        __basicBlockSuccessors = new HashMap<Integer, Set<Integer>>();
    }


    public CFG(){
        initializeData();

    }
    public CFG(Integer id){
        initializeData();
        __ID = id;
        __UniqueIDs = __ID++;
    }
    public CFG(Integer id, NestedSymbolTable table){
        initializeData();
        __symbolTable = table;
        __ID = id;
        __UniqueIDs = __ID++;
    }



    public Integer ID() { return __ID; }
    public Integer getNewID() { return __UniqueIDs++;}
    private void AddBasicBlock(BasicBlock block) {
        __basicBlocks.add(block);
    }

    public BasicBlock newBasicBlock() {
        NestedSymbolTable newTable = new NestedSymbolTable();
        newTable.setParent(__symbolTable);
        BasicBlock ret = new BasicBlock(this.getNewID(), newTable);
        this.AddBasicBlock(ret);

        return ret;
    }


    public void insertInstructionNode(BasicBlock bb, Instruction instruction, Boolean isLeader) {
        InstructionNode node = new InstructionNode(this.getNewID(),instruction,isLeader);
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
        this.addPredecessor(source,destination);
        this.addSuccessor(source,destination);
    }

    private void addPredecessor(BasicBlock source, BasicBlock destination){
        Set predecessorSet;
        if (__basicBlockPredecessors.containsKey(destination.ID())){
            predecessorSet = __basicBlockPredecessors.get(destination.ID());
        }
        else
            predecessorSet = new HashSet();
        predecessorSet.add(source.ID());
        __basicBlockPredecessors.put(destination.ID(),predecessorSet);
    }
    private void addSuccessor(BasicBlock source, BasicBlock destination) {
        Set successorSet;
        if (__basicBlockSuccessors.containsKey(source.ID())){
            successorSet = __basicBlockSuccessors.get(source.ID());
        }
        else
            successorSet = new HashSet();
        successorSet.add(destination.ID());
        __basicBlockSuccessors.put(destination.ID(),successorSet);
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
    //public void addDefinition(String key) {
    //    this.addDefinition(key,0);
    //}

    public void addResolution(String key, Variable variable, Boolean isGlobal){
        ChemicalResolution resolution = ResolveVariable(variable);
        resolution.setisGlobal(isGlobal);
        __symbolTable.put(key,resolution);
    }

    public ChemicalResolution ResolveVariable(Variable variable) {
        if(__symbolTable.contains(variable.getID()))
            return __symbolTable.get(variable.getID());

        ChemicalResolution resolution = new ChemicalResolution(variable.getName());
        if(variable instanceof Instance) {
            logger.info("Found Instance Literal");
            resolution.setIsLiteral(false);
        }

        for(Substance v : variable.getSubstance().values()) {
            resolution.addReference(ResolveSubstance(v));
        }
        return resolution;
    }

    private ChemicalResolution ResolveSubstance(Substance substance){
        if(__symbolTable.contains(substance.getName()))
            return __symbolTable.get(substance.getName());

        ChemicalResolution resolution = new ChemicalResolution(substance.getName());
        resolution.setIsLiteral(true);
        for(Chemical c: substance.getChemicals().values())
            resolution.addLiteral(c);

        __symbolTable.put(substance.getName(),resolution);
        return resolution;
    }

    /*public void addUse(String key, Integer opID) {
        List<Integer> opIDs;
        if (__useTable.containsKey(key)) {
            opIDs = __useTable.get(key);
        }
        else {
            opIDs = new ArrayList<Integer>();
        }
        opIDs.add(opID);

        __useTable.put(key,opIDs);
    }*/

    public NestedSymbolTable getSymbolTable() { return __symbolTable; }
    public void setSymbolTable(NestedSymbolTable table) { __symbolTable = table; }

    public HashMap<String, List<Integer> > getDefintionTable() { return __instructionDefinintionTable; }
    /*public HashMap<String, List<Integer> > getUseTable() { return  __useTable; }*/
    public List<InstructionNode> getInstructions() { return __instructions; }
    public List<BasicBlock> getBasicBlocks() { return __basicBlocks; }
    public BasicBlock getBasicBlock(Integer id) {
        for(BasicBlock bb :this.__basicBlocks) {
            if(bb.ID() == id){
                return bb;
            }
        }
        return null;
    }
    public List<BasicBlockEdge> getBasicBlockEdges() { return __edges; }
    public Set<Integer> getPredecessors(Integer basicBlockID) {
        return __basicBlockPredecessors.get(basicBlockID);
    }
    public Boolean hasPredecessors(Integer basicBlockID) {
        return __basicBlockPredecessors.containsKey(basicBlockID);
    }

    public Set<Integer> getSuccessors(Integer basicBlockID) {
        return __basicBlockSuccessors.get(basicBlockID);
    }


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

    public String toJSONString(){
        List<InstructionNode> instructions = new ArrayList<InstructionNode>();
        Map<Integer, Set<Integer>> childern = new HashMap<Integer, Set<Integer>>();

        for(BasicBlock bb : this.__basicBlocks){
            for(InstructionNode node : bb.getInstructions()){
                instructions.add(node);
            }
        }


        String ret = "";

        return ret;
    }
}