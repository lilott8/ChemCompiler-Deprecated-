package compilation.datastructures.ssa.semiprunedssa;

import java.util.HashSet;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.node.InstructionNode;
import compilation.datastructures.ssa.StaticSingleAssignment;

/**
 * Created by chriscurtis on 3/24/17.
 */
public class SemiPrunedStaticSingleAssignment extends StaticSingleAssignment {
    private HashSet<String> nonLocals = new HashSet<>();


    public SemiPrunedStaticSingleAssignment(CFG controlFlow) {
        super(controlFlow);

        this.createBasicBlockSymbolDefinitionAndUseTables();
        this.calculateNonLocalVariables();
        this.placePhiNodes(this.nonLocals);
        this.renameVariables();
    }


    private void calculateNonLocalVariables() {

        this.nonLocals.clear();

        for (BasicBlock bb : this.basicBlocks.values()) {
            bb.getKilledSet().clear();

            for (InstructionNode node : bb.getInstructions()) {
                for (String symbol : node.getInputSymbols()) {
                    if (!bb.getKilledSet().contains(symbol))
                        this.nonLocals.add(symbol);
                }

                for (String symbol : node.getOutputSymbols()) {
                    bb.getKilledSet().add(symbol);
                }
            }
        }

    }
}
