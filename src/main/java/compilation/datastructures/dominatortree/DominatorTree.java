package compilation.datastructures.dominatortree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import compilation.datastructures.cfg.CFG;

/**
 * Created by chriscurtis on 10/18/16.
 */
public class DominatorTree extends DominatorTreeBase {

    public DominatorTree(CFG controlFlowGraph) {

        __dominatorTable = new HashMap<Integer, List<Integer>>();
        __directionalSet = controlFlowGraph.getPredecessorTable(); //set predecessors
        __nodes = new ArrayList<Integer>();

        for (Integer bbID : controlFlowGraph.getBasicBlocks().keySet()) {
            __nodes.add(bbID);
        }

        BuildTree();
    }

    protected void BuildTree() {
        List<Integer> n_0 = new ArrayList<Integer>();
        n_0.add(__nodes.get(0));
        __dominatorTable.put(__nodes.get(0), n_0);
        for(int i =1 ; i<__nodes.size(); ++i) {
            __dominatorTable.put(__nodes.get(i),__nodes);
        }
        boolean changed;
        do {
            changed = false;
            for(int i = 1; i< __nodes.size();++i){
                List<Integer> currentSet = __dominatorTable.get(__nodes.get(i));
                List<Integer> newSet = super.DenominatorFormula(__nodes.get(i));
                if (!checkEq(newSet, currentSet)) {
                    changed = true;
                    __dominatorTable.put(__nodes.get(i),newSet);
                }
            }

        }while(changed);

        generateImmediateDominators();
        generateDominenceFrontier();
    }

}
