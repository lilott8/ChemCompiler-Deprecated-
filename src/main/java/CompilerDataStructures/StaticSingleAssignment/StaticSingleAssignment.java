package CompilerDataStructures.StaticSingleAssignment;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.DominatorTree.DominatorTree;
import CompilerDataStructures.InstructionNode;
import CompilerDataStructures.StaticSingleInformation.SigmaInstruction;

/**
 * Created by chriscurtis on 3/13/17.
 */
public abstract class StaticSingleAssignment extends CFG {
    public static Boolean DEBUGPHI = false;

    public static Boolean DEBUGLHS = false;
    public static Boolean DEBUGRHS = false;
    public static Boolean DEBUGPHIINSERT = false;

    public static Boolean DEBUG = false;


    protected DominatorTree __dominatorTree;
    protected HashMap<String, HashSet<Integer>> __basicBlockSymbolDefinitionTable;
    protected HashMap<String, HashSet<Integer>> __basicBlockSymbolUseTable;
    protected HashMap<String, HashSet<Integer>> __phiPlacedAt;



    protected HashMap<String, Stack<RenamedVariableNode> > __variableStack;
    protected HashMap<String, Integer> __variableCount;

    public HashMap<String, Stack<RenamedVariableNode>> get__variableStack() { return __variableStack; }


    public StaticSingleAssignment(CFG controlFlowGraph){
        super(controlFlowGraph);

        this.__dominatorTree = new DominatorTree(this);
        __basicBlockSymbolDefinitionTable = new HashMap<String, HashSet<Integer>>();
        __basicBlockSymbolUseTable = new HashMap<String, HashSet<Integer>>();
        __phiPlacedAt = new HashMap<String, HashSet<Integer>>();

        __variableStack = new HashMap<String, Stack<RenamedVariableNode>>();
        __variableCount = new HashMap<String, Integer>();
    }




    protected void CreateBasicBlockSymbolDefinitionAndUseTables(){
        //check for Global Variables



        for(InstructionNode instructionNode : this.__entry.getInstructions()){
            if(instructionNode instanceof GlobalAssignment){

                for(String symbol : instructionNode.getOutputSymbols()) {
                    logger.info( symbol);
                    if(this.__basicBlockSymbolDefinitionTable.containsKey(symbol)){
                        this.__basicBlockSymbolDefinitionTable.get(symbol).add(this.__entry.ID());
                    }
                    else {
                        HashSet<Integer> basicBlockList = new HashSet<Integer>();
                        basicBlockList.add(this.__entry.ID());
                        this.__basicBlockSymbolDefinitionTable.put(symbol,basicBlockList);
                    }
                }
            }
        }

        for(BasicBlock bb : this.__basicBlocks.values()) {

            for (InstructionNode node : bb.getInstructions())
                for (String symbol : node.getInputSymbols()) {
                    if (this.__basicBlockSymbolUseTable.containsKey(symbol)) {
                        this.__basicBlockSymbolUseTable.get(symbol).add(bb.ID());
                    }
                    else {
                        HashSet<Integer> basicBlockList = new HashSet<Integer>();
                        basicBlockList.add(bb.ID());
                        this.__basicBlockSymbolUseTable.put(symbol, basicBlockList);
                    }
                }
        }
        for(BasicBlock bb : this.__basicBlocks.values()){
            for(String symbol: bb.getDefinitions() ) {
                //System.out.println( symbol);
                if (this.__basicBlockSymbolDefinitionTable.containsKey(symbol)) {
                    this.__basicBlockSymbolDefinitionTable.get(symbol).add(bb.ID());
                }
                else {
                    HashSet<Integer> basicBlockList = new HashSet<Integer>();
                    basicBlockList.add(bb.ID());
                    this.__basicBlockSymbolDefinitionTable.put(symbol, basicBlockList);
                }
            }
        }

        //Establish the initial assignment in the Entry node.

        for(String symbol : this.__entry.getDefinitions()){
            this.__entry.addInstruction(new GlobalAssignment(symbol));
            this.__basicBlockSymbolDefinitionTable.get(symbol).add(this.__entry.ID());
        }
    }

    protected void RenameVariables(){
        if(DEBUG)
            logger.debug("Inital Symbols:");

        for(String symbol : __basicBlockSymbolDefinitionTable.keySet()){
            __variableCount.put(symbol,0);
            Stack<RenamedVariableNode> symbols = new Stack<RenamedVariableNode>();


            symbols.push(new RenamedVariableNode(symbol+"_0", 0) );
            if(DEBUG)
                logger.debug( "\t" + symbols.peek() );
            __variableStack.put(symbol, symbols);
        }
        this.RenameSearch(this.__entry);
    }

    protected void RenameSearch(BasicBlock bb){
        if (DEBUG)
            logger.debug("Processing Rename on: " + bb.ID());

        ArrayList<String> oldLHS = new ArrayList<String>();
        for(InstructionNode instruction : bb.getInstructions()){
            if(! (instruction instanceof PHIInstruction || instruction instanceof GlobalAssignment || instruction instanceof SigmaInstruction)){
                ArrayList<String> symbols= new ArrayList<String>();
                //needed deep copy to allow the removal of old symbols
                for(String symbol: instruction.Instruction().getInputs().keySet())
                    symbols.add(symbol);
                for(String symbol: symbols){
                    if(DEBUGRHS)
                        logger.debug("Changing RHS: " + symbol + " to " + __variableStack.get(symbol).peek());
                    int index  = instruction.getInputSymbols().indexOf(symbol);
                    instruction.getInputSymbols().set(index, __variableStack.get(symbol).peek().GetVariable(WhichSucc(bb.ID(),__variableStack.get(symbol).peek().getOrginID())));
//                    instruction.Instruction().getInputs().put(__variableStack.get(symbol).peek(),instruction.Instruction().getInputs().get(symbol));
//                    instruction.Instruction().getInputs().remove(symbol);
                }
            }
            ArrayList<String> newOutputSymbols = new ArrayList<String>();
            String oldSymbol = "";
            for(Integer i =0 ; i < instruction.getOutputSymbols().size(); ++i){
                oldSymbol = instruction.getOutputSymbols().get(i);
                oldLHS.add(oldSymbol);
                Integer count = __variableCount.get(oldSymbol);
                Integer predecessorID = __variableStack.get(oldSymbol).peek().getOrginID();
                String newSymbol = GetNewSymbol(__variableStack.get(oldSymbol).peek().GetVariable(WhichSucc(bb.ID(), predecessorID)),count);
                if(DEBUGLHS)
                    logger.debug("Changing LHS: " +oldSymbol + " to " + newSymbol);
                instruction.getOutputSymbols().set(i,newSymbol);
                if(instruction instanceof SigmaInstruction)
                    newOutputSymbols.add(newSymbol);
                else
                    __variableStack.get(oldSymbol).push(new RenamedVariableNode(newSymbol,bb.ID()));
                __variableCount.put(oldSymbol,count+1);
            }
            if(instruction instanceof SigmaInstruction)
                __variableStack.get(oldSymbol).push(new RenamedVariableNode(newOutputSymbols,bb.ID()));
        }
        if(this.getSuccessors(bb.ID()) != null ) {
            for (Integer successorID : this.getSuccessors(bb.ID())) {
                BasicBlock successor = this.getBasicBlock(successorID);
                Integer j = WhichPred(successorID, bb.ID());

                for (InstructionNode instructionNode : successor.getInstructions()) {
                    if (instructionNode instanceof PHIInstruction) {
                        String name = ((PHIInstruction) instructionNode).getOriginalName();
                        if(DEBUGPHIINSERT)
                            logger.debug("Inserting PHI: " +  __variableStack.get(name).peek() + " at index: " + j);
                        String PHIInputSymbol = __variableStack.get(name).peek().GetVariable(WhichSucc(successorID, bb.ID()));
                        ((PHIInstruction) instructionNode).InsertNodeAtIndex(j, PHIInputSymbol);
                    }
                }
            }
        }


        for(Integer child : this.__dominatorTree.getChildren(bb.ID())){
            RenameSearch(this.getBasicBlock(child));
        }

        for(String symbol : oldLHS){
            if(__variableStack.get(symbol).peek().CanPop())
                __variableStack.get(symbol).pop();
        }
    }



    protected Boolean PlacePhiNodes(){
        return this.PlacePhiNodes(null);
    }

    /*protected Boolean PlacePhiNodes(HashSet<String> symbols){
        Integer iterationCount = 0;

        HashMap<Integer, Integer> work = new HashMap<Integer, Integer>();
        HashMap<Integer, Integer> hasAlready = new HashMap<Integer, Integer>();

        for(Integer bbID : this.__basicBlocks.keySet()){
            work.put(bbID, 0);
            hasAlready.put(bbID,0);
        }

        ArrayList<Integer> WorkList = new ArrayList<Integer>();

        for(String symbol: __basicBlockSymbolDefinitionTable.keySet()){
            iterationCount ++; // used to distinguish between which variable we are using for work/has already
            for(Integer bbID : this.__basicBlockSymbolDefinitionTable.get(symbol)){
                work.put(bbID, iterationCount);
                WorkList.add(bbID);
                System.out.println("Adding: " + bbID + " to worklist for Symbol: " + symbol);
            }

            while(WorkList.size() > 0){
                Integer basicBlockID = WorkList.get(0);
                WorkList.remove(0);
                for(Integer domFrontierBBID: this.__dominatorTree.getFrontier(basicBlockID)){
                    if( (hasAlready.get(domFrontierBBID) < iterationCount && symbols == null) || (hasAlready.get(domFrontierBBID) < iterationCount && symbol.contains(symbol))) {
                        //AddSigmaNode
                        if(DEBUGPHI)
                            logger.debug("Adding Phi node for:" + symbol + " at Basic Block:" + domFrontierBBID);
                        this.__basicBlocks.get(domFrontierBBID).addInstruction(new PHIInstruction(symbol,this.getPredecessors(domFrontierBBID).size()));
                        hasAlready.put(domFrontierBBID,iterationCount);
                        if(work.get(domFrontierBBID) < iterationCount){
                            work.put(domFrontierBBID, iterationCount);
                            System.out.println("Adding: " + domFrontierBBID + " to worklist");
                            WorkList.add(domFrontierBBID);
                        }
                    }
                }
            }
        }
        return false;
    }*/


    protected Boolean PlacePhiNodes(HashSet<String>symbols){
        Boolean changed = false;


        ArrayList<Integer> WorkList = new ArrayList<Integer>();

        for(String symbol: __basicBlockSymbolDefinitionTable.keySet()) {
            if (symbols != null && !symbols.contains(symbol))
                continue;

            for (Integer BBID : this.__basicBlockSymbolDefinitionTable.get(symbol)) {
                WorkList.add(BBID);
            }

            while (!WorkList.isEmpty()) {
                Integer basicBlockID = WorkList.get(0);
                WorkList.remove(0);
                for (Integer domFrontierBBID : this.__dominatorTree.getFrontier(basicBlockID)) {


                    if (!this.__phiPlacedAt.containsKey(symbol) || !this.__phiPlacedAt.get(symbol).contains(domFrontierBBID)) {
                        changed = true;
                        if (DEBUGPHI)
                            logger.debug("Adding Phi node for:" + symbol + " at Basic Block:" + domFrontierBBID);

                        this.__basicBlocks.get(domFrontierBBID).addInstruction(new PHIInstruction(symbol, this.getPredecessors(domFrontierBBID).size()));

                        //A_PHI[v] <- A_PHI[v] U {y}
                        if (this.__phiPlacedAt.containsKey(symbol))
                            this.__phiPlacedAt.get(symbol).add(domFrontierBBID);
                        else {
                            HashSet<Integer> IDS = new HashSet<Integer>();
                            IDS.add(domFrontierBBID);
                            this.__phiPlacedAt.put(symbol, IDS);
                        }


                        for (Integer pred : this.__basicBlockPredecessorSet.get(domFrontierBBID)) {
                            if (this.__basicBlockSymbolUseTable.containsKey(symbol))
                                this.__basicBlockSymbolUseTable.get(symbol).add(pred);
                            else {
                                HashSet<Integer> IDS = new HashSet<Integer>();
                                IDS.add(pred);
                                this.__basicBlockSymbolUseTable.put(symbol, IDS);
                            }
                        }


                        if (!this.__basicBlockSymbolDefinitionTable.containsKey(symbol) || !this.__basicBlockSymbolDefinitionTable.get(symbol).contains(domFrontierBBID)) {
                            if (this.__basicBlockSymbolDefinitionTable.containsKey(symbol))
                                this.__basicBlockSymbolDefinitionTable.get(symbol).add(domFrontierBBID);
                            else {
                                HashSet<Integer> IDS = new HashSet<Integer>();
                                IDS.add(domFrontierBBID);
                                this.__basicBlockSymbolDefinitionTable.put(symbol, IDS);
                            }

                            WorkList.add(domFrontierBBID);
                        }
                    }
                }

            }
        }
        return changed;
    }




    private Integer WhichPred(Integer successor, Integer predecessor){
        Integer count = 0;
        //get the parent of the success
        for(Integer pred : this.__basicBlockPredecessorSet.get(successor)){
            if(pred == predecessor)
                return count;
            ++count;
        }

        return -1;
    }
    private Integer WhichSucc(Integer successor, Integer predecessor){
        if(successor == predecessor)
            return -1;
        Integer count = 0;
        //get the parent of the success
        for(Integer succ : this.__basicBlockSuccessorSet.get(predecessor)){
            if(succ == successor)
                return count;
            ++count;
        }

        return -1;
    }

    private static String GetNewSymbol(String symbol, Integer subscript) throws IllegalArgumentException{
        if(!symbol.contains("_")) {
            throw new IllegalArgumentException("String " + symbol + " Must have an \'_\' followed by a number at the end of the Symbol.");
        }
        Integer IndexOfLastUndescore = symbol.lastIndexOf('_');

        return symbol.substring(0,IndexOfLastUndescore+1) + subscript.toString();
    }

    public HashMap<String, HashSet<Integer>> getBasicBlockSymbolDefinitionTable() { return __basicBlockSymbolDefinitionTable; }
    public HashMap<String, HashSet<Integer>> getBasicBlockSymbolUseTable() { return __basicBlockSymbolUseTable; }



}
