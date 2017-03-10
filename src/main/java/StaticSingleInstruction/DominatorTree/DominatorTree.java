package StaticSingleInstruction.DominatorTree;

import StaticSingleInstruction.BasicBlock.BasicBlock;
import StaticSingleInstruction.BasicBlock.BasicBlockEdge;
import StaticSingleInstruction.ControlFlowGraph.CFG;

import java.util.*;

/**
 * Created by chriscurtis on 10/18/16.
 */
public class DominatorTree {
    private HashMap<Integer, List<Integer>> __dominencefrontier;
    private HashMap<Integer, List<Integer>> __dominatorTable;
   // private CFG __controlFlowGraph;
    private HashMap<Integer, Set<Integer>> __predecesors;

    private HashMap<Integer, Integer> __idoms;
    private List<Integer> __nodes;


    public DominatorTree(CFG controlFlowGraph) {
        //__controlFlowGraph = controlFlowGraph;
        __dominatorTable = new HashMap<Integer, List<Integer>>();
        __predecesors = controlFlowGraph.getPredecessorTable();
        __nodes = new ArrayList<Integer>();

        for (Integer bbID : controlFlowGraph.getBasicBlocks().keySet()) {
            __nodes.add(bbID);
        }

        BuildTree();
    }

    public List<Integer> getFrontier(Integer basicBlockID) {
        if(this.__dominencefrontier.containsKey(basicBlockID))
            return this.__dominencefrontier.get(basicBlockID);
        return new ArrayList<Integer>();
    }

    public Integer getImmediateDominator(Integer bbID) { return __idoms.get(bbID); }
    public ArrayList<Integer> getChildren(Integer bbID) {
        ArrayList<Integer> ret = new ArrayList<Integer>();

        for(Integer child: this.__idoms.keySet()){
            if(this.__idoms.get(child) == bbID)
                ret.add(child);
        }

        return ret;
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

        for(Integer ID : __dominatorTable.get(__predecesors.get(node).toArray()[0]))
            workSet.add(ID);

        for(int i =1 ; i < __predecesors.get(node).size(); ++i )
        {

            //Integer predecesor = __predecesors.get(node).get(i);
            for(Integer ID : __dominatorTable.get(__predecesors.get(node).toArray()[i])){
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


   /* private void GenerateIterativeFrontier(){
        /*
            Randy Allen Ken Kennedy-Optimizing Compilers- Figure 4.8
            procedure iterateDom(G)
                //G = (N,E) is the input control flow graph, where
                // N is the set of basic blocks and
                // E is the set of control flow edges
                // dominators(b) is the set of dominators for block b
                foreach b ε N do dominators(b) = N;


                changed := true;
                while changed do begin
                    changed := false;
                    foreach b ε N do begin
                        newDoms := dominators(b);
                        foreach p ε predecessors(b) do
                            newDoms := newDoms ∩ dominators(p);
                            newDoms := newDoms ∪ {b};
                            if newDoms != dominators(b) then begin
                                dominators(b) := newDoms;
                                changed := true;
                            end
                        end
                    end
                end iterateDom

        for(Integer b : this.__dominatorTable.keySet()){

        }


    }*/

    public String toString() {
        String ret="";

        ret += "getID \t\t IDOM \t\t DOM FRONTIER \t\t DOM PATH \n";

        for(Integer i : __dominatorTable.keySet()){
            ret += (i) ;
            ret+=" \t\t " + (__idoms.get(i)) + "\t";

            if (__idoms!= null) {
                if (__dominencefrontier.containsKey(i)) {
                    ret += " \t\t ";
                    for (Integer id : __dominencefrontier.get(i))
                        ret += (id) + " ";
                }
                else {

                    ret += "\t\t\t";

                }
            }
            ret+= " \t\t\t\t";
            ret += " [";
            for( Integer id : __dominatorTable.get(i))
                ret += id + " ";
            ret += "]";


            ret+='\n';


        }



        return ret;
    }


}
