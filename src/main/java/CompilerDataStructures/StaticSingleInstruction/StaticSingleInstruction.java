package CompilerDataStructures.StaticSingleInstruction;

import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.DominatorTree.PostDominatorTree;
import CompilerDataStructures.StaticSingleAssignment.PHIInstruction;
import CompilerDataStructures.StaticSingleAssignment.StaticSingleAssignment;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Created by chriscurtis on 4/10/17.
 */
public class StaticSingleInstruction extends StaticSingleAssignment{
    private Boolean DEBUGSIGMA  = true;


    private PostDominatorTree __postDominatorTree;
    protected HashMap<String, HashSet<Integer>> __sigmaPlacedAt;


   // HashMap<Integer, Integer> hasAlready = new HashMap<Integer, Integer>();

    public StaticSingleInstruction(CFG controlFlowGraph){
        super(controlFlowGraph);
        __postDominatorTree = new PostDominatorTree(this);
        __sigmaPlacedAt = new HashMap<String, HashSet<Integer>>();

        CreateBasicBlockSymbolDefinitionAndUseTables();

        Boolean changesMade = true;
        while (changesMade){
            changesMade = false;
            if(this.PlacePhiNodes())
                changesMade = true;
            if(this.PlaceSigmaNodes())
                changesMade = true;
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
            if (symbols != null && !symbols.contains(symbol))
                continue;

            for (Integer BBID : this.__basicBlockSymbolUseTable.get(symbol)) {
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
}
