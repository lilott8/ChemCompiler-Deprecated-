package StaticSingleInstruction.StaticSingleAssignment;

import StaticSingleInstruction.BasicBlock.BasicBlock;
import StaticSingleInstruction.ControlFlowGraph.CFG;
import StaticSingleInstruction.DominatorTree.DominatorTree;
import StaticSingleInstruction.InstructionNode;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * Created by chriscurtis on 3/1/17.
 */


public class StaticSingleAssignment extends CFG {
    public static Boolean DEBUG = true;


    protected DominatorTree __dominatorTree;
    protected HashMap<String, ArrayList<Integer>> __basicBlockDefinintionTable;

    public StaticSingleAssignment(CFG controlFlowGraph){
        super(controlFlowGraph);
        this.__dominatorTree = new DominatorTree(this);
        __basicBlockDefinintionTable = new HashMap<String, ArrayList<Integer>>();

        this.createBasicBlockDefinitionList();
        this.PlacePhiNodes();
    }


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
                        if(DEBUG)
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


    private void createBasicBlockDefinitionList(){
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
    }
}
