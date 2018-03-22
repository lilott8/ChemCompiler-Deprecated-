package compilation.datastructures.ssa;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.dominatortree.DominatorTree;
import compilation.datastructures.node.InstructionNode;
import compilation.datastructures.ssi.SigmaInstruction;
import compilation.datastructures.ssi.StaticSingleInformation;
import config.ConfigFactory;

/**
 * Created by chriscurtis on 3/13/17.
 */
public abstract class StaticSingleAssignment extends CFG {
    private static final Logger logger = LogManager.getLogger(StaticSingleInformation.class);
    public static Boolean DEBUGPHI = false;
    public static Boolean DEBUGLHS = false;
    public static Boolean DEBUGRHS = false;
    public static Boolean DEBUGPHIINSERT = false;
    protected DominatorTree dominatorTree;
    protected Map<String, Set<Integer>> basicBlockSymbolDefinitionTable;
    protected Map<String, Set<Integer>> basicBlockSymbolUseTable;
    protected Map<String, Set<Integer>> phiPlacedAt;

    protected Map<String, Stack<RenamedVariableNode>> variableStack;
    protected Map<String, Integer> variableCount;

    public StaticSingleAssignment(CFG controlFlowGraph) {
        super(controlFlowGraph);

        this.dominatorTree = new DominatorTree(this);
        basicBlockSymbolDefinitionTable = new HashMap<>();
        basicBlockSymbolUseTable = new HashMap<>();
        phiPlacedAt = new HashMap<>();

        variableStack = new HashMap<>();
        variableCount = new HashMap<>();
    }

    private static String getNewSymbol(String symbol, Integer subscript) throws IllegalArgumentException {
        if (!symbol.contains("_")) {
            throw new IllegalArgumentException("String " + symbol + " Must have an \'_\' followed by a number at the end of the Symbol.");
        }
        Integer IndexOfLastUndescore = symbol.lastIndexOf('_');

        return symbol.substring(0, IndexOfLastUndescore + 1) + subscript.toString();
    }

    public Map<String, Stack<RenamedVariableNode>> getVariableStack() {
        return variableStack;
    }

    protected void createBasicBlockSymbolDefinitionAndUseTables() {
        //check for Global Variables
        for (InstructionNode instructionNode : this.entry.getInstructions()) {
            if (instructionNode instanceof GlobalAssignment) {

                for (String symbol : instructionNode.getOutputSymbols()) {
                    logger.info(symbol);
                    if (this.basicBlockSymbolDefinitionTable.containsKey(symbol)) {
                        this.basicBlockSymbolDefinitionTable.get(symbol).add(this.entry.getId());
                    } else {
                        Set<Integer> basicBlockList = new HashSet<>();
                        basicBlockList.add(this.entry.getId());
                        this.basicBlockSymbolDefinitionTable.put(symbol, basicBlockList);
                    }
                }
            }
        }

        for (BasicBlock bb : this.basicBlocks.values()) {
            for (InstructionNode node : bb.getInstructions())
                for (String symbol : node.getInputSymbols()) {
                    if (this.basicBlockSymbolUseTable.containsKey(symbol)) {
                        this.basicBlockSymbolUseTable.get(symbol).add(bb.getId());
                    } else {
                        Set<Integer> basicBlockList = new HashSet<>();
                        basicBlockList.add(bb.getId());
                        this.basicBlockSymbolUseTable.put(symbol, basicBlockList);
                    }
                }
        }

        for (BasicBlock bb : this.basicBlocks.values()) {
            for (String symbol : bb.getDefinitions()) {
                //System.out.println( symbol);
                if (this.basicBlockSymbolDefinitionTable.containsKey(symbol)) {
                    this.basicBlockSymbolDefinitionTable.get(symbol).add(bb.getId());
                } else {
                    Set<Integer> basicBlockList = new HashSet<>();
                    basicBlockList.add(bb.getId());
                    this.basicBlockSymbolDefinitionTable.put(symbol, basicBlockList);
                }
            }
        }

        //Establish the initial assignment in the Entry node.
        for (String symbol : this.entry.getDefinitions()) {
            this.entry.addInstruction(new GlobalAssignment(symbol));
            this.basicBlockSymbolDefinitionTable.get(symbol).add(this.entry.getId());
        }
    }

    protected void renameVariables() {
        if (ConfigFactory.getConfig().isDebug()) {
            //logger.debug("Initial Symbols:");
        }

        for (String symbol : basicBlockSymbolDefinitionTable.keySet()) {
            variableCount.put(symbol, 0);
            Stack<RenamedVariableNode> symbols = new Stack<RenamedVariableNode>();

            symbols.push(new RenamedVariableNode(symbol + "_0", 0));
            if (ConfigFactory.getConfig().isDebug()) {
                //logger.debug("\t" + symbols.peek());
            }
            variableStack.put(symbol, symbols);
        }
        this.renameSearch(this.entry);
    }

    protected void renameSearch(BasicBlock bb) {
        if (ConfigFactory.getConfig().isDebug()) {
            // logger.debug("Processing Rename on: " + bb.getId());
        }

        ArrayList<String> oldLHS = new ArrayList<String>();
        for (InstructionNode instruction : bb.getInstructions()) {
            if (!(instruction instanceof PHIInstruction || instruction instanceof GlobalAssignment || instruction instanceof SigmaInstruction)) {
                ArrayList<String> symbols = new ArrayList<String>();
                //needed deep copy to allow the removal of old symbols
                for (String symbol : instruction.getInstruction().getInputs().keySet())
                    symbols.add(symbol);
                for (String symbol : symbols) {
                    if (ConfigFactory.getConfig().isDebug()) {
                        // logger.debug("Changing RHS: " + symbol + " to " + variableStack.get(symbol).peek());
                    }
                    int index = instruction.getInputSymbols().indexOf(symbol);
                    logger.info(instruction);
                    instruction.getInputSymbols().set(index, variableStack.get(symbol).peek().getVariable(whichSucc(bb.getId(), variableStack.get(symbol).peek().getOriginID())));
//                    instruction.getInstruction().getInputs().put(variableStack.get(symbol).peek(),instruction.getInstruction().getInputs().get(symbol));
//                    instruction.getInstruction().getInputs().remove(symbol);
                }
            }
            ArrayList<String> newOutputSymbols = new ArrayList<String>();
            String oldSymbol = "";
            for (Integer i = 0; i < instruction.getOutputSymbols().size(); ++i) {
                oldSymbol = instruction.getOutputSymbols().get(i);
                oldLHS.add(oldSymbol);
                Integer count = variableCount.get(oldSymbol);
                Integer predecessorID = variableStack.get(oldSymbol).peek().getOriginID();
                String newSymbol = getNewSymbol(variableStack.get(oldSymbol).peek().getVariable(whichSucc(bb.getId(), predecessorID)), count);
                if (ConfigFactory.getConfig().isDebug()) {
                    // logger.debug("Changing LHS: " + oldSymbol + " to " + newSymbol);
                }
                instruction.getOutputSymbols().set(i, newSymbol);
                if (instruction instanceof SigmaInstruction) {
                    newOutputSymbols.add(newSymbol);
                } else {
                    variableStack.get(oldSymbol).push(new RenamedVariableNode(newSymbol, bb.getId()));
                }
                variableCount.put(oldSymbol, count + 1);
            }
            if (instruction instanceof SigmaInstruction) {
                variableStack.get(oldSymbol).push(new RenamedVariableNode(newOutputSymbols, bb.getId()));
            }
        }
        if (this.getSuccessors(bb.getId()) != null) {
            for (Integer successorID : this.getSuccessors(bb.getId())) {
                BasicBlock successor = this.getBasicBlock(successorID);
                Integer j = whichPred(successorID, bb.getId());

                for (InstructionNode instructionNode : successor.getInstructions()) {
                    if (instructionNode instanceof PHIInstruction) {
                        String name = ((PHIInstruction) instructionNode).getOriginalName();
                        if (ConfigFactory.getConfig().isDebug()) {
                            // logger.debug("Inserting PHI: " + variableStack.get(name).peek() + " at index: " + j);
                        }
                        String PHIInputSymbol = variableStack.get(name).peek().getVariable(whichSucc(successorID, bb.getId()));
                        ((PHIInstruction) instructionNode).insertNodeAtIndex(j, PHIInputSymbol);
                    }
                }
            }
        }


        for (Integer child : this.dominatorTree.getChildren(bb.getId())) {
            renameSearch(this.getBasicBlock(child));
        }

        for (String symbol : oldLHS) {
            if (variableStack.get(symbol).peek().canPop())
                variableStack.get(symbol).pop();
        }
    }

    protected Boolean placePhiNodes() {
        return this.placePhiNodes(null);
    }

    protected Boolean placePhiNodes(HashSet<String> symbols) {
        Boolean changed = false;


        List<Integer> WorkList = new ArrayList<>();

        for (String symbol : basicBlockSymbolDefinitionTable.keySet()) {
            if (symbols != null && !symbols.contains(symbol))
                continue;

            for (Integer BBID : this.basicBlockSymbolDefinitionTable.get(symbol)) {
                WorkList.add(BBID);
            }

            while (!WorkList.isEmpty()) {
                Integer basicBlockID = WorkList.get(0);
                WorkList.remove(0);
                for (Integer domFrontierBBID : this.dominatorTree.getFrontier(basicBlockID)) {


                    if (!this.phiPlacedAt.containsKey(symbol) || !this.phiPlacedAt.get(symbol).contains(domFrontierBBID)) {
                        changed = true;
                        if (ConfigFactory.getConfig().isDebug()) {
                            // logger.debug("Adding Phi node for:" + symbol + " at Basic Block:" + domFrontierBBID);
                        }

                        this.basicBlocks.get(domFrontierBBID).addInstruction(new PHIInstruction(symbol, this.getPredecessors(domFrontierBBID).size()));

                        //A_PHI[v] <- A_PHI[v] U {y}
                        if (this.phiPlacedAt.containsKey(symbol))
                            this.phiPlacedAt.get(symbol).add(domFrontierBBID);
                        else {
                            HashSet<Integer> IDS = new HashSet<Integer>();
                            IDS.add(domFrontierBBID);
                            this.phiPlacedAt.put(symbol, IDS);
                        }


                        for (Integer pred : this.basicBlockPredecessorSet.get(domFrontierBBID)) {
                            if (this.basicBlockSymbolUseTable.containsKey(symbol))
                                this.basicBlockSymbolUseTable.get(symbol).add(pred);
                            else {
                                HashSet<Integer> IDS = new HashSet<Integer>();
                                IDS.add(pred);
                                this.basicBlockSymbolUseTable.put(symbol, IDS);
                            }
                        }


                        if (!this.basicBlockSymbolDefinitionTable.containsKey(symbol) || !this.basicBlockSymbolDefinitionTable.get(symbol).contains(domFrontierBBID)) {
                            if (this.basicBlockSymbolDefinitionTable.containsKey(symbol))
                                this.basicBlockSymbolDefinitionTable.get(symbol).add(domFrontierBBID);
                            else {
                                HashSet<Integer> IDS = new HashSet<Integer>();
                                IDS.add(domFrontierBBID);
                                this.basicBlockSymbolDefinitionTable.put(symbol, IDS);
                            }

                            WorkList.add(domFrontierBBID);
                        }
                    }
                }

            }
        }
        return changed;
    }

    private Integer whichPred(Integer successor, Integer predecessor) {
        Integer count = 0;
        //get the parent of the success
        for (Integer pred : this.basicBlockPredecessorSet.get(successor)) {
            if (pred == predecessor)
                return count;
            ++count;
        }

        return -1;
    }

    private Integer whichSucc(Integer successor, Integer predecessor) {
        if (successor == predecessor)
            return -1;
        Integer count = 0;
        //get the parent of the success
        for (Integer succ : this.basicBlockSuccessorSet.get(predecessor)) {
            if (succ == successor)
                return count;
            ++count;
        }

        return -1;
    }

    public Map<String, Set<Integer>> getBasicBlockSymbolDefinitionTable() {
        return basicBlockSymbolDefinitionTable;
    }

    public Map<String, Set<Integer>> getBasicBlockSymbolUseTable() {
        return basicBlockSymbolUseTable;
    }


}
