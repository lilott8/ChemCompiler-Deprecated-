package DataFlow;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import CompilerDataStructures.BasicBlock.BasicBlockEdge;
import CompilerDataStructures.ControlFlowGraph.CFG;

/**
 * Created by chriscurtis on 10/19/16.
 */
abstract class DataFlowAnalysis {
    protected CFG __controlFlowGraph;
    protected HashMap<Integer,List<Integer>> __predecesors;
    protected HashMap<Integer,List<Integer>> __successors;

    public DataFlowAnalysis(CFG cfg) {

        __controlFlowGraph = cfg;


        __predecesors = new HashMap<Integer, List<Integer>>();
        __successors  = new HashMap<Integer, List<Integer>>();
        for(BasicBlockEdge edge: cfg.getBasicBlockEdges()) {
            List<Integer> preds;
            if (__predecesors.containsKey(edge.getDestination())) {
                preds = __predecesors.get(edge.getDestination());
            }
            else
                preds = new ArrayList<Integer>();
            preds.add(edge.getSource());
            __predecesors.put(edge.getDestination(),preds);

            List<Integer> successor;
            if (__successors.containsKey(edge.getDestination())) {
                successor = __successors.get(edge.getDestination());
            }
            else
                successor = new ArrayList<Integer>();
            successor.add(edge.getDestination());
            __successors.put(edge.getSource(),successor);
        }
    }

}
