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

    Map<Integer, ReachingDefinitionNode> finalAnswer;

    public ReachingDefinitions(CFG controlflowgraph) {
        super(controlflowgraph);

        Map<Integer, ReachingDefinitionNode> initialization = new HashMap<Integer, ReachingDefinitionNode>();

        for(BasicBlock bb: controlflowgraph.getBasicBlocks().values()){
            initialization.put(bb.ID(),new ReachingDefinitionNode(bb));
        }

        boolean changed = true;
        while(changed) {
            changed = false;
           // Map<Integer, ReachingDefinitionNode> nextIteration = new HashMap<Integer, ReachingDefinitionNode>();
            for(ReachingDefinitionNode node : initialization.values()){
                List<ReachingDefinitionNode> predecessors = new ArrayList<ReachingDefinitionNode>();

                HashMap<Integer,List<Integer>> p = this.predecesors;
                if(p.containsKey(node.id))
                    for (Integer predecesorID : p.get(node.id))
                        predecessors.add(initialization.get(predecesorID));

                ReachingDefinitionNode n = new ReachingDefinitionNode(node);
                if(n.addIn(predecessors,this.controlFlowGraph.getSymbolTable(), initialization))
                    changed = true;
                initialization.put(n.id,n);
            }

//            initialization.clear();
            //initialization.putAll(nextIteration);
            //nextIteration.clear();

        }

        //final update on out
        for(ReachingDefinitionNode n: initialization.values()) {
            n.getOut();
        }


        finalAnswer = initialization;

    }

    public String toString(){
        String ret = "";
        for(Integer i : finalAnswer.keySet()){
            ret += i + "\n";
            ret += finalAnswer.get(i).toString() +'\n';
        }
        return ret;
    }



}
