package compilation.datastructures.ssi;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import compilation.datastructures.cfg.CFG;
import compilation.datastructures.dominatortree.PostDominatorTree;
import compilation.datastructures.ssa.StaticSingleAssignment;

/**
 * Created by chriscurtis on 4/10/17.
 */
public class StaticSingleInformation extends StaticSingleAssignment{
    private Boolean DEBUGSIGMA  = false;


    private PostDominatorTree __postDominatorTree;
    protected HashMap<String, HashSet<Integer>> __sigmaPlacedAt;


   // HashMap<Integer, Integer> hasAlready = new HashMap<Integer, Integer>();

    public StaticSingleInformation(CFG controlFlowGraph){
        super(controlFlowGraph);
        __postDominatorTree = new PostDominatorTree(controlFlowGraph);
        __sigmaPlacedAt = new HashMap<String, HashSet<Integer>>();

        CreateBasicBlockSymbolDefinitionAndUseTables();

        Boolean changesMade = true;
        while (changesMade){
            changesMade = false;
            if(this.PlacePhiNodes())
                changesMade = true;
           // logger.debug(this);
            if(this.PlaceSigmaNodes())
                changesMade = true;
            //logger.debug(this);
        }

        this.RenameVariables();


    }

    protected Boolean PlaceSigmaNodes(){
        return this.PlaceSigmaNodes(null);
    }

    protected Boolean PlaceSigmaNodes(HashSet<String> symbols) {

        Boolean changed = false;


        ArrayList<Integer> WorkList = new ArrayList<Integer>();

        for (String symbol : this.__basicBlockSymbolDefinitionTable.keySet()) {
            if (symbols != null && !symbols.contains(symbol) || !this.__basicBlockSymbolUseTable.containsKey(symbol))
                continue;

            for (Integer BBID : this.__basicBlockSymbolUseTable.get(symbol)) {
                if(!WorkList.contains(BBID))
                    WorkList.add(BBID);
            }

            while (!WorkList.isEmpty()) {
                Integer basicBlockID = WorkList.get(0);
                WorkList.remove(0);
                for (Integer domFrontierBBID : this.__postDominatorTree.getFrontier(basicBlockID)) {


                    if (!this.__sigmaPlacedAt.containsKey(symbol) || !this.__sigmaPlacedAt.get(symbol).contains(domFrontierBBID)) {
                        changed = true;
                        if (DEBUGSIGMA)
                            logger.debug("Adding Sigma node for:" + symbol + " at Basic Block:" + domFrontierBBID);

                        this.__basicBlocks.get(domFrontierBBID).addInstruction(new SigmaInstruction(symbol,this.getSuccessors(domFrontierBBID).size()));

                        //A_SIGMA[v] <- A_SIGMA[v] U {y}
                        if (this.__sigmaPlacedAt.containsKey(symbol))
                            this.__sigmaPlacedAt.get(symbol).add(domFrontierBBID);
                        else {
                            HashSet<Integer> IDS = new HashSet<Integer>();
                            IDS.add(domFrontierBBID);
                            this.__sigmaPlacedAt.put(symbol, IDS);
                        }


                        for (Integer succ : this.__basicBlockSuccessorSet.get(domFrontierBBID)) {
                            if (this.__basicBlockSymbolDefinitionTable.containsKey(symbol))
                                this.__basicBlockSymbolDefinitionTable.get(symbol).add(succ);
                            else {
                                HashSet<Integer> IDS = new HashSet<Integer>();
                                IDS.add(succ);
                                this.__basicBlockSymbolDefinitionTable.put(symbol, IDS);
                            }
                        }


                        if (!this.__basicBlockSymbolUseTable.containsKey(symbol) || !this.__basicBlockSymbolUseTable.get(symbol).contains(domFrontierBBID)) {
                            if (this.__basicBlockSymbolUseTable.containsKey(symbol))
                                this.__basicBlockSymbolUseTable.get(symbol).add(domFrontierBBID);
                            else {
                                HashSet<Integer> IDS = new HashSet<Integer>();
                                IDS.add(domFrontierBBID);
                                this.__basicBlockSymbolUseTable.put(symbol, IDS);
                            }

                            WorkList.add(domFrontierBBID);
                        }
                    }
                }

            }
        }
        return changed;
    }
   /* protected void RenameVariables(){
        if(DEBUG)
            logger.debug("Inital Symbols:");

        for(String symbol : __basicBlockSymbolDefinitionTable.keySet()){
            __variableCount.put(symbol,0);
            Stack<String> symbols = new Stack<String>();
            symbols.push(symbol+"_0");
            if(DEBUG)
                logger.debug( "\t" + symbols.peek() );
            __variableStack.put(symbol, symbols);
        }
        this.RenameSearch(this.__entry);

    }

    protected void RenameSearch(basicblock bb){
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
                basicblock successor = this.getBasicBlock(successorID);
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
    }*/
}
