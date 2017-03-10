package StaticSingleInstruction.StaticSingleAssignment;

import StaticSingleInstruction.BasicBlock.BasicBlock;
import StaticSingleInstruction.ControlFlowGraph.CFG;
import StaticSingleInstruction.DominatorTree.DominatorTree;
import StaticSingleInstruction.InstructionNode;
import jdk.nashorn.internal.runtime.Debug;

import java.util.*;

/**
 * Created by chriscurtis on 3/1/17.
 */


public class StaticSingleAssignment extends CFG {
    //ToDO:: consider modifing the InstructionNode to Process Instruciton and capture Input/Output Symbol this will allow for renameing symobls inplace

    public static Boolean DEBUGPHI = false;
    public static Boolean DEBUG = true;

    public static Boolean DEBUGLHS = false;
    public static Boolean DEBUGRHS = false;
    public static Boolean DEBUGPHIINSERT = true;




    protected DominatorTree __dominatorTree;
    protected HashMap<String, ArrayList<Integer>> __basicBlockDefinintionTable;

    protected HashMap<String, Stack<String> > __variableStack;
    protected HashMap<String, Integer> __variableCount;

    public StaticSingleAssignment(CFG controlFlowGraph){
        super(controlFlowGraph);
        this.__dominatorTree = new DominatorTree(this);
        __basicBlockDefinintionTable = new HashMap<String, ArrayList<Integer>>();
        __variableStack = new HashMap<String, Stack<String>>();
        __variableCount = new HashMap<String, Integer>();

        this.createBasicBlockDefinitionList();
        this.PlacePhiNodes();
        this.RenameVariables();
    }

    private void createBasicBlockDefinitionList(){
        //check for Gloabal Variables
        for(InstructionNode instructionNode : this.__entry.getInstructions()){
            if(instructionNode instanceof StaticAssignment){
                for(String symbol : instructionNode.getOutputSymbols()) {
                    if(this.__basicBlockDefinintionTable.containsKey(symbol)){
                        this.__basicBlockDefinintionTable.get(symbol).add(this.__entry.ID());
                    }
                    else {
                        ArrayList<Integer> basicBlockList = new ArrayList<Integer>();
                        basicBlockList.add(this.__entry.ID());
                        this.__basicBlockDefinintionTable.put(symbol,basicBlockList);
                    }
                }
            }
        }


        for(BasicBlock bb : this.__basicBlocks.values()){
            for(String symbol: bb.getDefinitions() )
                if(this.__basicBlockDefinintionTable.containsKey(symbol)){
                    this.__basicBlockDefinintionTable.get(symbol).add(bb.ID());
                }
                else {
                    ArrayList<Integer> basicBlockList = new ArrayList<Integer>();
                    basicBlockList.add(bb.ID());
                    this.__basicBlockDefinintionTable.put(symbol,basicBlockList);
                }
        }

        //Establish the initial assignment in the Entry node.

        for(String symbol : this.__basicBlockDefinintionTable.keySet()){
            this.__entry.addInstruction(new StaticAssignment(symbol));
            this.__basicBlockDefinintionTable.get(symbol).add(this.__entry.ID());
        }
    }

    private void RenameVariables(){
        if(DEBUG)
            logger.debug("Inital Symbols:");

        for(String symbol : __basicBlockDefinintionTable.keySet()){
            __variableCount.put(symbol,0);
            Stack<String> symbols = new Stack<String>();
            symbols.push(symbol+"_0");
            if(DEBUG)
                logger.debug( "\t" + symbols.peek() );
            __variableStack.put(symbol, symbols);
        }
        this.RenameSearch(this.__entry);
    }

    private void RenameSearch(BasicBlock bb){
        if (DEBUG)
           logger.debug("Processing Rename on: " + bb.ID());

       ArrayList<String> oldLHS = new ArrayList<String>();
        for(InstructionNode instruction : bb.getInstructions()){
            if(! (instruction instanceof PHIInstruction || instruction instanceof StaticAssignment)){
                ArrayList<String> symbols= new ArrayList<String>();
                //needed deep copy to allow the removal of old symbols
                for(String symbol: instruction.Instruction().getInputs().keySet())
                    symbols.add(symbol);
                for(String symbol: symbols){
                    if(DEBUGRHS)
                        logger.debug("Changing RHS: " + symbol + " to " + __variableStack.get(symbol).peek());
                    int index  = instruction.getInputSymbols().indexOf(symbol);
                    instruction.getInputSymbols().set(index, __variableStack.get(symbol).peek());
//                    instruction.Instruction().getInputs().put(__variableStack.get(symbol).peek(),instruction.Instruction().getInputs().get(symbol));
//                    instruction.Instruction().getInputs().remove(symbol);
                }
            }
            for(Integer i =0 ; i < instruction.getOutputSymbols().size(); ++i){
                String oldSymbol = instruction.getOutputSymbols().get(i);
                oldLHS.add(oldSymbol);
                Integer count = __variableCount.get(oldSymbol);
                String newSymbol = GetNewSymbol(__variableStack.get(oldSymbol).peek(), count);
                if(DEBUGLHS)
                    logger.debug("Changing LHS: " +oldSymbol + " to " + newSymbol);
                instruction.getOutputSymbols().set(i,newSymbol);
                __variableStack.get(oldSymbol).push(newSymbol);
                __variableCount.put(oldSymbol,count+1);
            }
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
                        ((PHIInstruction) instructionNode).InsertNodeAtIndex(j, __variableStack.get(name).peek());
                    }
                }
            }
        }


        for(Integer child : this.__dominatorTree.getChildren(bb.ID())){
            RenameSearch(this.getBasicBlock(child));
        }

        for(String symbol : oldLHS){
            __variableStack.get(symbol).pop();
        }
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

    private static String GetNewSymbol(String symbol, Integer subscript) throws IllegalArgumentException{
        if(!symbol.contains("_")) {
            throw new IllegalArgumentException("String " + symbol + " Must have an \'_\' followed by a number at the end of the Symbol.");
        }
        Integer IndexOfLastUndescore = symbol.lastIndexOf('_');

        return symbol.substring(0,IndexOfLastUndescore+1) + subscript.toString();
    }
/*    private static String GetOldSymbol(String symbol) throws IllegalArgumentException{
        if(!symbol.contains("_")) {
            throw new IllegalArgumentException("String" + symbol + " Must have an \'_\' followed by a number at the end of the Symbol.");
        }
        Integer IndexOfLastUndescore = symbol.lastIndexOf('_');

        return symbol.substring(0,IndexOfLastUndescore+1) ;
    }*/


    private void PlacePhiNodes(){
        Integer iterationCount = 0;

        HashMap<Integer, Integer> work = new HashMap<Integer, Integer>();
        HashMap<Integer, Integer> hasAlready = new HashMap<Integer, Integer>();

        for(Integer bbID : this.__basicBlocks.keySet()){
            work.put(bbID, 0);
            hasAlready.put(bbID,0);
        }

        ArrayList<Integer> WorkList = new ArrayList<Integer>();

        for(String symbol: __basicBlockDefinintionTable.keySet()){
            iterationCount ++; // used to distinguish between which variable we are using for work/has already
            for(Integer bbID : this.__basicBlockDefinintionTable.get(symbol)){
                work.put(bbID, iterationCount);
                WorkList.add(bbID);
            }

            while(WorkList.size() > 0){
                Integer basicBlockID = WorkList.get(0);
                WorkList.remove(0);
                for(Integer domFrontierBBID: this.__dominatorTree.getFrontier(basicBlockID)){
                    if(hasAlready.get(domFrontierBBID) < iterationCount) {
                        //AddPhiNode
                        if(DEBUGPHI)
                            logger.debug("Adding Phi node for:" + symbol + " at Basic Block:" + domFrontierBBID);
                        this.__basicBlocks.get(domFrontierBBID).addInstruction(new PHIInstruction(symbol));
                        hasAlready.put(domFrontierBBID,iterationCount);
                        if(work.get(domFrontierBBID) < iterationCount){
                            work.put(domFrontierBBID, iterationCount);
                            WorkList.add(domFrontierBBID);
                        }
                    }
                }
            }
        }
    }


}





    /*public void addDefinition(String key, Integer opID) {
        List<Integer> opIDs;
        if (__instructionDefinintionTable.containsKey(key)) {
            opIDs = __instructionDefinintionTable.get(key);
        }
        else {
            opIDs = new ArrayList<Integer>();
        }
        opIDs.add(opID);

        __instructionDefinintionTable.put(key,opIDs);
    }*/

    /*
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
*/