package compilation.datastructures.cfg;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import chemical.ChemicalResolution;
import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.BasicBlockEdge;
import compilation.datastructures.node.InstructionNode;
import compilation.symboltable.NestedSymbolTable;
import executable.instructions.Instruction;
import substance.Chemical;
import substance.Substance;
import variable.Instance;
import variable.Variable;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class CFG implements Serializable {
    public static final Logger logger = LogManager.getLogger(CFG.class);

    //private UndirectedGraph<BasicBlock, DefaultEdge> statements = new SimpleGraph<>(DefaultEdge.class);

    protected Map<Integer, BasicBlock> basicBlocks = new LinkedHashMap<>();
    protected BasicBlock entry;
    protected BasicBlock exit;
    protected List<BasicBlockEdge> edges = new ArrayList<>();
    protected Map<Integer, Set<Integer>> basicBlockPredecessorSet = new HashMap<>();
    protected Map<Integer, Set<Integer>> basicBlockSuccessorSet = new HashMap<>();
    protected NestedSymbolTable symbolTable = new NestedSymbolTable();
    protected Integer uuid = 0;
    protected Integer id = 1;

    public CFG(CFG controlFlowGraph) {
        this.basicBlocks = controlFlowGraph.basicBlocks;
        this.edges = controlFlowGraph.edges;
        this.basicBlockPredecessorSet = controlFlowGraph.basicBlockPredecessorSet;
        this.basicBlockSuccessorSet = controlFlowGraph.basicBlockSuccessorSet;
        this.symbolTable = controlFlowGraph.symbolTable;
        this.uuid = controlFlowGraph.uuid;
        this.id = controlFlowGraph.id;
        this.entry = controlFlowGraph.entry;
        this.exit = controlFlowGraph.exit;
    }

    public CFG() {
    }

    public CFG(Integer id) {
        this.id = id;
        uuid = this.id++;
    }

    public CFG(Integer id, NestedSymbolTable table) {
        symbolTable = table;
        this.id = id;
        uuid = this.id++;
    }

    public Integer getID() {
        return id;
    }

    public Integer getNewID() {
        return uuid++;
    }

    private void addBasicBlock(BasicBlock block) {
        basicBlocks.put(block.getId(), block);
    }

    public BasicBlock getEntry() {
        return entry;
    }

    public void setEntry(BasicBlock entry) {
        this.entry = entry;
    }

    public BasicBlock getExit() {
        return exit;
    }

    public void setExit(BasicBlock exit) {
        this.exit = exit;
    }

    public BasicBlock newBasicBlock() {
        NestedSymbolTable newTable = new NestedSymbolTable();
        newTable.setParent(symbolTable);
        BasicBlock ret = new BasicBlock(this.getNewID(), newTable);
        this.addBasicBlock(ret);

        return ret;
    }

    public void newBasicBlock(BasicBlock bb) {
        this.addBasicBlock(bb);
    }


    public void insertInstructionNode(BasicBlock bb, Instruction instruction, Boolean isLeader) {
        InstructionNode node = new InstructionNode(this.getNewID(), instruction, isLeader);
        bb.addInstruction(node);
    }

    public void addEdge(BasicBlock source, BasicBlock destination) {
        this.addEdge(source, destination, "UNCONDITIONAL");
    }

    public void addEdge(BasicBlock source, BasicBlock destination, String condition) {
        edges.add(new BasicBlockEdge(source.getId(), destination.getId(), condition));
        this.addPredecessor(source, destination);
        this.addSuccessor(source, destination);
    }

    public void addEdge(BasicBlock source, BasicBlock destination, String condition, String name) {
        edges.add(new BasicBlockEdge(source.getId(), destination.getId(), condition, name));
        this.addPredecessor(source, destination);
        this.addSuccessor(source, destination);
    }

    private void addPredecessor(BasicBlock source, BasicBlock destination) {
        Set predecessorSet;
        if (basicBlockPredecessorSet.containsKey(destination.getId())) {
            predecessorSet = basicBlockPredecessorSet.get(destination.getId());
        } else
            predecessorSet = new HashSet();
        predecessorSet.add(source.getId());
        basicBlockPredecessorSet.put(destination.getId(), predecessorSet);
    }

    private void addSuccessor(BasicBlock source, BasicBlock destination) {
        Set successorSet;

        if (basicBlockSuccessorSet.containsKey(source.getId())) {
            successorSet = basicBlockSuccessorSet.get(source.getId());
        } else
            successorSet = new HashSet();
        successorSet.add(destination.getId());
        basicBlockSuccessorSet.put(source.getId(), successorSet);
    }

    public void addResolution(String key, Variable variable, Boolean isGlobal) {
        ChemicalResolution resolution = resolveVariable(variable);
        resolution.setisGlobal(isGlobal);
        if (variable instanceof Instance) {
            resolution.setIsStationary(((Instance) variable).getIsStationary());
        }
        symbolTable.put(key, resolution);
    }

    public ChemicalResolution resolveVariable(Variable variable) {
        if (symbolTable.contains(variable.getID()))
            return symbolTable.get(variable.getID());

        ChemicalResolution resolution = new ChemicalResolution(variable.getName());
        if (variable instanceof Instance) {
            //logger.info("Found Instance Literal");
            resolution.setIsLiteral(false);
        }

        // for(Substance v : variable.getSubstance().values()) {
        //     resolution.addReference(resolveSubstance(v));
        // }
        return resolution;
    }

    private ChemicalResolution resolveSubstance(Substance substance) {
        if (symbolTable.contains(substance.getName()))
            return symbolTable.get(substance.getName());

        ChemicalResolution resolution = new ChemicalResolution(substance.getName());
        resolution.setIsLiteral(true);
        for (Chemical c : substance.getChemicals().values())
            resolution.addLiteral(c);

        symbolTable.put(substance.getName(), resolution);
        return resolution;
    }


    public NestedSymbolTable getSymbolTable() {
        return symbolTable;
    }

    public void setSymbolTable(NestedSymbolTable table) {
        symbolTable = table;
    }

    public Map<Integer, BasicBlock> getBasicBlocks() {
        return basicBlocks;
    }

    public BasicBlock getBasicBlock(Integer id) {
        return this.basicBlocks.get(id);
    }

    public BasicBlock getBasicBlockByInstructionID(Integer id) {
        for (BasicBlock bb : basicBlocks.values()) {
            if (bb.containsInstruction(id)) {
                return bb;
            }
        }
        return null;
    }

    public List<BasicBlockEdge> getBasicBlockEdges() {
        return edges;
    }

    public List<BasicBlockEdge> getBasicBlockEdgesBySource(int source) {
        List<BasicBlockEdge> _ret = new ArrayList<>();
        for (BasicBlockEdge e : edges) {
            if (e.getSource() == source)
                _ret.add(e);
        }
        return _ret;
    }

    public List<BasicBlockEdge> getBasicBlockEdgesByDest(int dest) {
        List<BasicBlockEdge> _ret = new ArrayList<>();
        for (BasicBlockEdge e : edges) {
            if (e.getDestination() == dest)
                _ret.add(e);
        }
        return _ret;
    }

    public Map<Integer, Set<Integer>> getPredecessorTable() {
        return this.basicBlockPredecessorSet;
    }

    public Set<Integer> getPredecessors(Integer basicBlockID) {
        return basicBlockPredecessorSet.get(basicBlockID);
    }

    public Boolean hasPredecessors(Integer basicBlockID) {
        return basicBlockPredecessorSet.containsKey(basicBlockID);
    }

    public Set<Integer> getSuccessors(Integer basicBlockID) {
        return basicBlockSuccessorSet.get(basicBlockID);
    }

    public Map<Integer, Set<Integer>> getSuccessorTable() {
        return basicBlockSuccessorSet;
    }

    public String toString() {
        return this.toString("");
    }

    public String toString(String indentBuffer) {
        String ret = indentBuffer + "CFG: \n";
        for (BasicBlock bb : this.basicBlocks.values()) {
            ret += bb.toString(indentBuffer + '\t') + '\n';
        }
        ret += indentBuffer + "CFG Edges: \n";
        for (BasicBlockEdge edge : edges) {
            ret += edge.toString(indentBuffer + '\t') + '\n';
        }

        ret += "\n SYMBOL TABLE\n";
        ret += symbolTable.toString();
        return ret;
    }
}