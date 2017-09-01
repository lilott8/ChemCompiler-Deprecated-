package compilation.datastructures.ssa.minimumssa;

import compilation.datastructures.cfg.CFG;
import compilation.datastructures.ssa.StaticSingleAssignment;


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
