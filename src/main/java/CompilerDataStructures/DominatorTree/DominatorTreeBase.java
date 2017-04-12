package CompilerDataStructures.DominatorTree;

import java.util.*;

/**
 * Created by chriscurtis on 4/4/17.
 */
abstract class DominatorTreeBase {
    protected HashMap<Integer, List<Integer>> __dominencefrontier;
    protected HashMap<Integer, List<Integer>> __dominatorTable;


    //this directional set holds the predecessors or the successors for the dominator Trees:
    // Predecessors for Dominator
    // Successors for  PostDominator
    protected HashMap<Integer, Set<Integer>> __directionalSet;

    protected HashMap<Integer, Integer> __idoms;
    protected List<Integer> __nodes;



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


    protected List<Integer> DenominatorFormula(Integer node){
        HashSet<Integer> newSet = new HashSet<Integer>();
        HashSet<Integer> workSet = new HashSet<Integer>();

        for(Integer ID : __dominatorTable.get(__directionalSet.get(node).toArray()[0]))
            workSet.add(ID);

        for(int i = 1; i < __directionalSet.get(node).size(); ++i )
        {

            //Integer predecesor = __directionalSet.get(node).get(i);
            for(Integer ID : __dominatorTable.get(__directionalSet.get(node).toArray()[i])){
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


    protected void generateImmediateDominators(){
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

    protected static Boolean checkEq(List a, List b){
        if(a.size() != b.size() )
            return false;
        for(int i = 0; i< a.size(); ++i) {
            if(a.get(i)!=b.get(i))
                return false;
        }
        return true;
    }

    protected void generateDominenceFrontier(){
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
            if (__directionalSet.containsKey(bb)) {
                if (__directionalSet.get(bb).size() >= 2) {
                    for (Integer pred_or_Succ : __directionalSet.get(bb)) {
                        Integer runner = pred_or_Succ;
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
