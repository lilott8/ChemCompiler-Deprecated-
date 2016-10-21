package DataFlow;

import CFGBuilder.BasicBlock;
import CFGBuilder.CFG;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by chriscurtis on 10/19/16.
 */
public class ReachingDefinitions extends DataFlowAnalysis {

    Map<Integer, ReachingDefinitionNode> __finalAnswer;

    public ReachingDefinitions(CFG controlflowgraph) {
        super(controlflowgraph);


        Map<Integer, ReachingDefinitionNode> initialization = new HashMap<Integer, ReachingDefinitionNode>();

        for(BasicBlock bb: controlflowgraph.getBasicBlocks()){
            initialization.put(bb.ID(),new ReachingDefinitionNode(bb));
        }

        Boolean changed = true;
        while(changed) {
            changed = false;
            Map<Integer, ReachingDefinitionNode> nextIteration = new HashMap<Integer, ReachingDefinitionNode>();
            for(ReachingDefinitionNode node : initialization.values()){
                List<ReachingDefinitionNode> predecessors = new ArrayList<ReachingDefinitionNode>();
                for (Integer predecesorID : this.__predecesors.get(node.__ID))
                    predecessors.add(initialization.get(predecesorID));

                ReachingDefinitionNode n = new ReachingDefinitionNode(node);
                if(node.addIN(predecessors,this.__controlFlowGraph.getSymbolTable()))
                    changed = true;
                nextIteration.put(n.__ID,n);
            }

            initialization.clear();
            initialization.putAll(nextIteration);
            nextIteration.clear();

        }

        __finalAnswer = initialization;

    }



}
