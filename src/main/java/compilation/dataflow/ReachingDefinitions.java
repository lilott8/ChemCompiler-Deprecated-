package compilation.dataflow;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.cfg.CFG;

/**
 * Created by chriscurtis on 10/19/16.
 */
public class ReachingDefinitions extends DataFlowAnalysis {

    Map<Integer, ReachingDefinitionNode> __finalAnswer;

    public ReachingDefinitions(CFG controlflowgraph) {
        super(controlflowgraph);


        Map<Integer, ReachingDefinitionNode> initialization = new HashMap<Integer, ReachingDefinitionNode>();

        for(BasicBlock bb: controlflowgraph.getBasicBlocks().values()){
            initialization.put(bb.ID(),new ReachingDefinitionNode(bb));
        }

        Boolean changed = true;
        while(changed) {
            changed = false;
           // Map<Integer, ReachingDefinitionNode> nextIteration = new HashMap<Integer, ReachingDefinitionNode>();
            for(ReachingDefinitionNode node : initialization.values()){
                List<ReachingDefinitionNode> predecessors = new ArrayList<ReachingDefinitionNode>();

                HashMap<Integer,List<Integer>> p = this.__predecesors;
                if(p.containsKey(node.__ID))
                    for (Integer predecesorID : p.get(node.__ID))
                        predecessors.add(initialization.get(predecesorID));

                ReachingDefinitionNode n = new ReachingDefinitionNode(node);
                if(n.addIN(predecessors,this.__controlFlowGraph.getSymbolTable(), initialization))
                    changed = true;
                initialization.put(n.__ID,n);
            }

//            initialization.clear();
            //initialization.putAll(nextIteration);
            //nextIteration.clear();

        }

        //final update on out
        for(ReachingDefinitionNode n: initialization.values()) {
            n.getOut();
        }


        __finalAnswer = initialization;

    }

    public String toString(){
        String ret = "";
        for(Integer i : __finalAnswer.keySet()){
            ret += i + "\n";
            ret += __finalAnswer.get(i).toString() +'\n';
        }
        return ret;
    }



}
