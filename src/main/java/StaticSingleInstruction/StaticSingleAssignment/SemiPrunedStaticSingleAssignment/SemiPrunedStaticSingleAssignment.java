package StaticSingleInstruction.StaticSingleAssignment.SemiPrunedStaticSingleAssignment;

import StaticSingleInstruction.BasicBlock.BasicBlock;
import StaticSingleInstruction.ControlFlowGraph.CFG;
import StaticSingleInstruction.InstructionNode;
import StaticSingleInstruction.StaticSingleAssignment.SingleStaticAssignment;

import java.util.HashSet;

/**
 * Created by chriscurtis on 3/24/17.
 */
public class SemiPrunedStaticSingleAssignment extends SingleStaticAssignment {
    private HashSet<String> __nonLocals;


    public SemiPrunedStaticSingleAssignment(CFG controlFlow){
        super(controlFlow);

        __nonLocals = new HashSet<String>();

        this.CreateBasicBlockDefinitionList();
        this.CalculateNonLocalVariables();
        this.PlacePhiNodes(this.__nonLocals);
        this.RenameVariables();
    }



    private void CalculateNonLocalVariables(){

        this.__nonLocals.clear();

        for(BasicBlock bb : this.__basicBlocks.values()){
            bb.getKilledSet().clear();

            for(InstructionNode node : bb.getInstructions()) {
                for (String symbol : node.getInputSymbols()){
                    if (!bb.getKilledSet().contains(symbol))
                        this.__nonLocals.add(symbol);
                }

                for(String symbol: node.getOutputSymbols()){
                    bb.getKilledSet().add(symbol);
                }
            }
        }

    }
}
