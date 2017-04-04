package StaticSingleInstruction.StaticSingleAssignment.MinimalStaticSingleAssignment;

import StaticSingleInstruction.ControlFlowGraph.CFG;
import StaticSingleInstruction.StaticSingleAssignment.SingleStaticAssignment;


/**
 * Created by chriscurtis on 3/1/17.
 */


public class MinimalStaticSingleAssignment extends SingleStaticAssignment {

    public MinimalStaticSingleAssignment(CFG controlFlowGraph){
        super(controlFlowGraph);

        this.CreateBasicBlockDefinitionList();
        this.PlacePhiNodes();
        this.RenameVariables();
    }


}
