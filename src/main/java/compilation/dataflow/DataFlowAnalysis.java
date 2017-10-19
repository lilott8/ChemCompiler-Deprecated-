package compilation.dataflow;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import compilation.datastructures.basicblock.BasicBlockEdge;
import compilation.datastructures.cfg.CFG;

/**
 * Created by chriscurtis on 10/19/16.
 */
abstract class DataFlowAnalysis {
    protected CFG controlFlowGraph;
    protected HashMap<Integer,List<Integer>> predecesors;
    protected HashMap<Integer,List<Integer>> successors;

    public DataFlowAnalysis(CFG cfg) {
        controlFlowGraph = cfg;
        predecesors = new HashMap<>();
        successors = new HashMap<>();
        for(BasicBlockEdge edge: cfg.getBasicBlockEdges()) {
            List<Integer> preds;
            if (predecesors.containsKey(edge.getDestination())) {
                preds = predecesors.get(edge.getDestination());
            }
            else {
                preds = new ArrayList<>();
            }
            preds.add(edge.getSource());
            predecesors.put(edge.getDestination(),preds);

            List<Integer> successor;
            if (successors.containsKey(edge.getDestination())) {
                successor = successors.get(edge.getDestination());
            }
            else {
                successor = new ArrayList<>();
            }
            successor.add(edge.getDestination());
            successors.put(edge.getSource(),successor);
        }
    }

}
