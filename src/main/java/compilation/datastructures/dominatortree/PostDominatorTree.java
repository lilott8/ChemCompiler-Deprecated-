package compilation.datastructures.dominatortree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import compilation.datastructures.cfg.CFG;

/**
 * Created by chriscurtis on 4/4/17.
 */
public class PostDominatorTree extends DominatorTreeBase {

    public PostDominatorTree(CFG controlFlowGraph) {

        dominatorTable = new HashMap<>();

        directionalSet = controlFlowGraph.getSuccessorTable(); //set successors

        nodes = new ArrayList<>();

        //this needs to the Exit Node to be the LAST Node.
        //The Exit node will have the largest getId

        Integer maxID = -1;
        for (Integer bbID : controlFlowGraph.getBasicBlocks().keySet()) {
            if (maxID < bbID) {
                maxID = bbID;
            }
            nodes.add(bbID);
        }
        //move max to end of list.
        nodes.remove(nodes.indexOf(maxID));
        nodes.add(maxID);

        buildTree();
    }

    protected void buildTree() {
        List<Integer> n_n = new ArrayList<>();

        n_n.add(nodes.get(nodes.size() - 1));
        dominatorTable.put(nodes.get(nodes.size() - 1), n_n);

        for (int i = nodes.size() - 2; i >= 0; --i) {
            dominatorTable.put(nodes.get(i), nodes);
        }
        boolean changed;
        do {
            changed = false;
            for (int i = nodes.size() - 2; i >= 0; --i) {
                List<Integer> currentSet = dominatorTable.get(nodes.get(i));
                List<Integer> newSet = super.denominatorFormula(nodes.get(i));
                if (!checkEq(newSet, currentSet)) {
                    changed = true;
                    dominatorTable.put(nodes.get(i), newSet);
                }
            }

        } while (changed);

        generateImmediateDominators();
        generateDominanceFrontier();
    }

}
