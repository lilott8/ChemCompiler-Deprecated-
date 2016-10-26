package Translators;

import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.CFG;
import ControlFlowGraph.InstructionEdge;
import ControlFlowGraph.InstructionNode;

import java.util.*;

/**
 * Created by chriscurtis on 10/26/16.
 */
public class TypeSystemTanslator {
    private List<InstructionNode> __instructions;
    private Map<Integer, Set<Integer>> __children;

    public TypeSystemTanslator(CFG controlFlowGraph) {
        __instructions = new ArrayList<InstructionNode>();
        __children = new HashMap<Integer, Set<Integer>>();

        for(BasicBlock bb : controlFlowGraph.getBasicBlocks()) {
            for (InstructionNode node : bb.getInstructions()) {
                __instructions.add(node);
            }
            for (InstructionEdge edge : bb.getEdges()) {
                if(__children.containsKey(edge.getSource())){
                    __children.get(edge.getSource()).add(edge.getDestination());
                }
                else {
                    Set<Integer> children = new HashSet<Integer>();
                    children.add(edge.getDestination());
                    __children.put(edge.getSource(),children);
                }
            }
        }
    }

    public String toString(){
        String ret = "\n";
        for(InstructionNode n : __instructions) {
            ret += n.toString() + '\n';
        }
        for(Integer parent : __children.keySet()) {
            ret += parent + ": ";
            for(Integer child : __children.get(parent))
                ret += child + " ";
            ret+="\n";
        }
        return ret;
    }

}

