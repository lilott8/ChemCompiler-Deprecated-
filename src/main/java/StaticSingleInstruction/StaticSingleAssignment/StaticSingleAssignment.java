package StaticSingleInstruction.StaticSingleAssignment;

import StaticSingleInstruction.ControlFlowGraph.CFG;
import StaticSingleInstruction.DominatorTree.DominatorTree;

import java.util.HashMap;
import java.util.List;

/**
 * Created by chriscurtis on 3/1/17.
 */
public class StaticSingleAssignment extends CFG {

    private DominatorTree __dominatorTree;
    protected HashMap<String, List<Integer> > __instructionDefinintionTable;

public StaticSingleAssignment(CFG controlFlowGraph){
    super(controlFlowGraph);
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

}
