package CompilerDataStructures.StaticSingleAssignment.MinimalStaticSingleAssignment;

import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.StaticSingleAssignment.StaticSingleAssignment;


/**
 * Created by chriscurtis on 3/1/17.
 */


public class MinimalStaticSingleAssignment extends StaticSingleAssignment {

    public MinimalStaticSingleAssignment(CFG controlFlowGraph){
        super(controlFlowGraph);

        this.CreateBasicBlockSymbolDefinitionAndUseTables();
        this.PlacePhiNodes();
        this.RenameVariables();
    }


}
