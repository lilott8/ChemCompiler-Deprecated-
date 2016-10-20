package DominatorTree;

import CFGBuilder.BasicBlock;
import CFGBuilder.BasicBlockEdge;
import CFGBuilder.CFG;
import CFGBuilder.InstructionNode;

import java.util.*;

/**
 * Created by chriscurtis on 10/18/16.
 */
public class DominatorTree {
    private HashMap<Integer, List<Integer>> __dominencefrontier;
    private HashMap<Integer, List<Integer>> __dominatorTable;
    private HashMap<Integer, List<Integer>> __predecesors;
    private HashMap<Integer, Integer> __idoms;
    private List<Integer> __nodes;


    public DominatorTree(CFG controlFlowGraph) {
        __dominatorTable = new HashMap<Integer, List<Integer>>();
        __predecesors = new HashMap<Integer, List<Integer>>();
        __nodes = new ArrayList<Integer>();

        for (BasicBlock bb : controlFlowGraph.getBasicBlocks()) {
            __nodes.add(bb.ID());
        }
        for(BasicBlockEdge edge: controlFlowGraph.getBasicBlockEdges()) {
            List<Integer> preds;
            if (__predecesors.containsKey(edge.getDestination())) {
                preds = __predecesors.get(edge.getDestination());
            }
            else
                preds = new ArrayList<Integer>();
            preds.add(edge.getSource());
            __predecesors.put(edge.getDestination(),preds);
        }
        BuildTree();
    }
    private void BuildTree() {
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
                List<Integer> newSet = DominatorFormula(__nodes.get(i));
                if( !checkEq(newSet, currentSet)) {
                    changed = true;
                    __dominatorTable.put(__nodes.get(i),newSet);
                }
            }

        }while(changed);

        generateImmediateDominators();
        generateDominenceFrontier();
    }
    private List<Integer> DominatorFormula(Integer node){
        HashSet<Integer> newSet = new HashSet<Integer>();
        HashSet<Integer> workSet = new HashSet<Integer>();

        for(Integer ID : __dominatorTable.get(__predecesors.get(node).get(0)))
            workSet.add(ID);

        for(int i =1 ; i < __predecesors.get(node).size(); ++i )
        {

            //Integer predecesor = __predecesors.get(node).get(i);
            for(Integer ID : __dominatorTable.get(__predecesors.get(node).get(i))){
                if(workSet.contains(ID))
                    newSet.add(ID);
            }
            workSet.clear();
            for(Integer id :newSet)
                workSet.add(id);
            newSet.clear();
        }
        workSet.add(node);
        List<Integer> ret = new ArrayList<Integer>();

        for(Integer i : workSet)
            ret.add(i);
        Collections.sort(ret);
        return ret;
    }
    private Boolean checkEq(List a, List b){
        if(a.size() != b.size() )
            return false;
        for(int i = 0; i< a.size(); ++i) {
            if(a.get(i)!=b.get(i))
                return false;
        }
        return true;
    }

    private void generateImmediateDominators(){
        __idoms = new HashMap<Integer, Integer>();
        for(Integer dominatedKey: __dominatorTable.keySet()) {
            List<Integer> dominators = new ArrayList<Integer>();
            for(Integer dominator : __dominatorTable.get(dominatedKey) ) {
                if (dominator != dominatedKey) {
                    dominators.add(dominator);
                }
            }
            if(dominators.size() == 0)
                __idoms.put(0,-1);

            for(Integer dominator : dominators) {
                if (checkEq(dominators,__dominatorTable.get(dominator)))
                    __idoms.put(dominatedKey,dominator);
            }
        }
    }

    private void generateDominenceFrontier(){
    /*   for each B in all basic blocks
            if size of Predecessors(B) >= 2
                for each P in Predecessors(B)
                    runner = P
                    while runner != idom[B]    # idom is the immediate dominator
                        DF(runner) += B
                        runner = idom[runner]
                        */
        __dominencefrontier = new HashMap<Integer, List<Integer>>();
        for(Integer bb : __nodes) {
            if (__predecesors.containsKey(bb)) {
                if (__predecesors.get(bb).size() >= 2) {
                    for (Integer predececor : __predecesors.get(bb)) {
                        Integer runner = predececor;
                        while (runner != null && runner != __idoms.get(bb) && runner != -1) {
                            List<Integer> frontier;
                            if (__dominencefrontier.containsKey(runner))
                                frontier = __dominencefrontier.get(runner);
                            else
                                frontier = new ArrayList<Integer>();
                            frontier.add(bb);
                            __dominencefrontier.put(runner, frontier);
                            runner = __idoms.get(runner);
                        }
                    }
                }
            }
        }
    }

    public String toString() {
        String ret="";
        for(Integer i : __dominatorTable.keySet()){
            ret += (i+1) + " [";
            for( Integer id : __dominatorTable.get(i))
                ret += id+1 + " ";
            ret+="] IDOM: " + (__idoms.get(i)+1);

            if (__idoms!= null) {
                if (__dominencefrontier.containsKey(i)) {
                    ret += " DomFrontier: ";
                    for (Integer id : __dominencefrontier.get(i))
                        ret += (id + 1) + " ";
                }
            }

            ret+='\n';


        }



        return ret;
    }


}
