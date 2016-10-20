package DataFlow;

import CFGBuilder.BasicBlock;
import CFGBuilder.CFG;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 10/19/16.
 */
abstract class DataFlowAnalysis {
    private CFG __controlFlowGraph;

    public DataFlowAnalysis(CFG cfg) {
        __controlFlowGraph = cfg;
    }

}
