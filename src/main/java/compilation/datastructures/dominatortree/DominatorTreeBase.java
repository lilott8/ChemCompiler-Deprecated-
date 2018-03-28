package compilation.datastructures.dominatortree;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by chriscurtis on 4/4/17.
 */
abstract class DominatorTreeBase {
    public static final Logger logger = LogManager.getLogger(DominatorTreeBase.class);
    protected Map<Integer, List<Integer>> dominanceFrontier;
    protected Map<Integer, List<Integer>> dominatorTable;
    //this directional set holds the predecessors or the successors for the dominator Trees:
    // Predecessors for Dominator
    // Successors for  PostDominator
    protected Map<Integer, Set<Integer>> directionalSet;
    protected Map<Integer, Integer> iDoms;
    protected List<Integer> nodes;

    protected static Boolean checkEq(List a, List b) {
        if (a.size() != b.size())
            return false;
        for (int i = 0; i < a.size(); ++i) {
            if (a.get(i) != b.get(i))
                return false;
        }
        return true;
    }

    public List<Integer> getFrontier(Integer basicBlockID) {
        if (this.dominanceFrontier.containsKey(basicBlockID)) {
            return this.dominanceFrontier.get(basicBlockID);
        }
        return new ArrayList<>();
    }

    public Integer getImmediateDominator(Integer bbID) {
        return iDoms.get(bbID);
    }

    public List<Integer> getChildren(Integer bbID) {
        List<Integer> ret = new ArrayList<>();

        for (Integer child : this.iDoms.keySet()) {
            if (this.iDoms.get(child) == bbID) {
                ret.add(child);
            }
        }

        return ret;
    }

    protected List<Integer> denominatorFormula(Integer node) {
        Set<Integer> newSet = new HashSet<>();
        Set<Integer> workSet = new HashSet<>();

        workSet.addAll(dominatorTable.get(directionalSet.get(node).toArray()[0]));

        for (int i = 1; i < directionalSet.get(node).size(); ++i) {
            //Integer predecesor = __directionalSet.get(node).get(i);
            for (Integer ID : dominatorTable.get(directionalSet.get(node).toArray()[i])) {
                if (workSet.contains(ID))
                    newSet.add(ID);
            }
            workSet.clear();
            workSet.addAll(newSet);
            newSet.clear();
        }
        workSet.add(node);
        List<Integer> ret = new ArrayList<>(workSet);
        Collections.sort(ret);
        return ret;
    }

    protected void generateImmediateDominators() {
        iDoms = new HashMap<>();
        for (int dominatedKey : dominatorTable.keySet()) {
            List<Integer> dominators = new ArrayList<>();
            for (int dominator : dominatorTable.get(dominatedKey)) {
                if (dominator != dominatedKey) {
                    dominators.add(dominator);
                }
            }
            if (dominators.size() == 0)
                iDoms.put(0, -1);

            for (int dominator : dominators) {
                if (checkEq(dominators, dominatorTable.get(dominator)))
                    iDoms.put(dominatedKey, dominator);
            }
        }
    }

    protected void generateDominanceFrontier() {
        dominanceFrontier = new HashMap<>();
        for (Integer bb : nodes) {
            if (directionalSet.containsKey(bb)) {
                if (directionalSet.get(bb).size() >= 2) {
                    for (int predOrSucc : directionalSet.get(bb)) {
                        Integer runner = predOrSucc;
                        while (runner != null && runner != iDoms.get(bb) && runner != -1) {
                            List<Integer> frontier;
                            if (dominanceFrontier.containsKey(runner)) {
                                frontier = dominanceFrontier.get(runner);
                            } else {
                                frontier = new ArrayList<>();
                            }
                            frontier.add(bb);
                            dominanceFrontier.put(runner, frontier);
                            runner = iDoms.get(runner);
                        }
                    }
                }
            }
        }
    }

    public String toString() {
        String ret = "";

        ret += "getID \t\t IDOM \t\t DOM FRONTIER \t\t DOM PATH \n";

        for (Integer i : dominatorTable.keySet()) {
            ret += (i);
            ret += " \t\t " + (iDoms.get(i)) + "\t";

            if (iDoms != null) {
                if (dominanceFrontier.containsKey(i)) {
                    ret += " \t\t ";
                    for (Integer id : dominanceFrontier.get(i))
                        ret += (id) + " ";
                } else {

                    ret += "\t\t\t";

                }
            }
            ret += " \t\t\t\t";
            ret += " [";
            for (Integer id : dominatorTable.get(i))
                ret += id + " ";
            ret += "]";
            ret += '\n';
        }
        return ret;
    }
}
