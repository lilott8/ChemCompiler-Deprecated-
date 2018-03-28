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
        dominatorTable = new HashMap<>();
        directionalSet = controlFlowGraph.getPredecessorTable(); //set predecessors
        nodes = new ArrayList<Integer>();

        for (Integer bbID : controlFlowGraph.getBasicBlocks().keySet()) {
            nodes.add(bbID);
        }

        buildTree();
    }

    protected void buildTree() {
        List<Integer> n_0 = new ArrayList<Integer>();
        n_0.add(nodes.get(0));
        dominatorTable.put(nodes.get(0), n_0);
        for (int i = 1; i < nodes.size(); ++i) {
            dominatorTable.put(nodes.get(i), nodes);
        }
        boolean changed;
        do {
            changed = false;
            for (int i = 1; i < nodes.size(); ++i) {
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
