package compilation.dataflow;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.symboltable.NestedSymbolTable;

/**
 * Created by chriscurtis on 10/19/16.
 */
public class ReachingDefinitionNode extends DataFlowNode {

    public ReachingDefinitionNode(BasicBlock bb){
        super(bb);

    }
    public ReachingDefinitionNode(ReachingDefinitionNode node){
        super(node.__ID);
        this.__gen = node.__gen;
        this.__kill = node.__kill;

    }

    public Boolean addIN(List< ReachingDefinitionNode> predecessors, NestedSymbolTable table, Map<Integer, ReachingDefinitionNode> prevRound ){
        Boolean flag = false;
        for(ReachingDefinitionNode predecessor : predecessors)
            for(String predecessorOut : predecessor.getOut()) {
                if(!prevRound.get(__ID).__in.contains(predecessorOut))
                    flag = true;
                if(!this.__in.contains(predecessorOut))
                    this.__in.add(predecessorOut);



                if (this.__gen.contains(predecessorOut)) {
                    this.__kill.add(predecessorOut);
                    flag = true;
                }

                else if (table.getPointsTo().containsKey(predecessorOut)) {
                    String oldName = table.getPointsTo().get(predecessorOut);
                    if (this.__gen.contains(oldName)) {
                        this.__kill.add(predecessorOut);
                        flag = true;
                    }
                }
            }
        return flag;
    }
    public List<String> getOut(){
        List<String> ret = new ArrayList<String>();

        for(String gen : this.__gen) {
            ret.add(gen);
        }

        for(String input: this.__in){
            if(!this.__kill.contains(input))
                ret.add(input);
        }
        this.__out = ret;
        return ret;
    }


}
