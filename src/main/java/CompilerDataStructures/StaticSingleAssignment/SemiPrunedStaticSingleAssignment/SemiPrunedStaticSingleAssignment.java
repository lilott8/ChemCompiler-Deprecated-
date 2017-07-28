package CompilerDataStructures.StaticSingleAssignment.SemiPrunedStaticSingleAssignment;

import java.util.HashSet;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.InstructionNode;
import CompilerDataStructures.StaticSingleAssignment.StaticSingleAssignment;

/**
 * Created by chriscurtis on 3/24/17.
 */
public class SemiPrunedStaticSingleAssignment extends StaticSingleAssignment {
    private HashSet<String> __nonLocals;


    public SemiPrunedStaticSingleAssignment(CFG controlFlow){
        super(controlFlow);

        __nonLocals = new HashSet<String>();

        this.CreateBasicBlockSymbolDefinitionAndUseTables();
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
