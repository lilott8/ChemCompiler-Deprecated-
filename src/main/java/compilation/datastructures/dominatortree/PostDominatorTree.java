package compilation.datastructures.dominatortree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import compilation.datastructures.cfg.CFG;

/**
 * Created by chriscurtis on 4/4/17.
 */
public class PostDominatorTree extends DominatorTreeBase {

    public PostDominatorTree(CFG controlFlowGraph){

        __dominatorTable = new HashMap<Integer, List<Integer>>();

        __directionalSet = controlFlowGraph.getSuccessorTable(); //set successors

        __nodes = new ArrayList<Integer>();

        //this needs to the Exit Node to be the LAST Node.
        //The Exit node will have the largest ID

        Integer maxID=-1;
        for (Integer bbID : controlFlowGraph.getBasicBlocks().keySet()) {
            if(maxID < bbID){
                maxID = bbID;
            }
            __nodes.add(bbID);
        }
        //move max to end of list.
        __nodes.remove(__nodes.indexOf(maxID));
        __nodes.add(maxID);

        BuildTree();
    }

    protected void BuildTree() {
        List<Integer> n_n = new ArrayList<Integer>();



        n_n.add(__nodes.get(__nodes.size()-1));
        __dominatorTable.put(__nodes.get(__nodes.size()-1), n_n);

        for(int i = __nodes.size()-2 ; i>=0; --i) {
            __dominatorTable.put(__nodes.get(i),__nodes);
        }
        boolean changed;
        do {
            changed = false;
            for(int i = __nodes.size()-2; i>=0 ;--i){
                List<Integer> currentSet = __dominatorTable.get(__nodes.get(i));
                List<Integer> newSet = super.DenominatorFormula(__nodes.get(i));
                if( !super.checkEq(newSet, currentSet)) {
                    changed = true;
                    __dominatorTable.put(__nodes.get(i),newSet);
                }
            }

        }while(changed);

        generateImmediateDominators();
        generateDominenceFrontier();
    }

}
