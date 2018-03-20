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

    public ReachingDefinitionNode(BasicBlock bb) {
        super(bb);

    }

    public ReachingDefinitionNode(ReachingDefinitionNode node) {
        super(node.id);
        this.gen = node.gen;
        this.kill = node.kill;

    }

    public Boolean addIn(List<ReachingDefinitionNode> predecessors, NestedSymbolTable table, Map<Integer, ReachingDefinitionNode> prevRound) {
        boolean flag = false;
        for (ReachingDefinitionNode predecessor : predecessors)
            for (String predecessorOut : predecessor.getOut()) {
                if (!prevRound.get(id).in.contains(predecessorOut)) {
                    flag = true;
                }
                if (!this.in.contains(predecessorOut)) {
                    this.in.add(predecessorOut);
                }

                if (this.gen.contains(predecessorOut)) {
                    this.kill.add(predecessorOut);
                    flag = true;
                } else if (table.getPointsTo().containsKey(predecessorOut)) {
                    String oldName = table.getPointsTo().get(predecessorOut);
                    if (this.gen.contains(oldName)) {
                        this.kill.add(predecessorOut);
                        flag = true;
                    }
                }
            }
        return flag;
    }

    public List<String> getOut() {
        List<String> ret = new ArrayList<String>();

        for (String gen : this.gen) {
            ret.add(gen);
        }

        for (String input : this.in) {
            if (!this.kill.contains(input))
                ret.add(input);
        }
        this.out = ret;
        return ret;
    }


}
