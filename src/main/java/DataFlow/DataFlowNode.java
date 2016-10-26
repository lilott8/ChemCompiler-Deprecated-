package DataFlow;

import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.InstructionNode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Created by chriscurtis on 10/19/16.
 */
abstract public class DataFlowNode {
    protected Integer __ID;
    protected Set<String> __gen;
    protected Set<String> __kill;
    protected List<String> __out;
    protected List<String> __in;

    public DataFlowNode(Integer id){
        __ID = id;
        __gen = null;
        __kill = null;
        __in = new ArrayList<String>();
        __out = new ArrayList<String>();
    }
    public DataFlowNode(BasicBlock bb) {
        __gen = new HashSet<String>();
        __kill = new HashSet<String>();
        __in = new ArrayList<String>();
        __out = new ArrayList<String>();
        __ID = bb.ID();


        for(InstructionNode i :bb.getInstructions()) {
            for(String out: i.Instruction().getOutputs().keySet())
                __gen.add(out);
        }



    }
    public String toString() {
        String ret = "";
        if(__gen!= null && __gen.size()>0) {
            ret += "Gen: ";
            for (String item : __gen) {
                ret += item + " ";
            }
            ret += '\n';
        }
        if(__kill!= null && __kill.size()>0) {
            ret += "Kill: ";
            for (String item : __kill) {
                ret += item + " ";
            }
            ret += '\n';
        }
        if(__out!= null && __out.size()>0) {
            ret += "Out: ";
            for (String item : __out) {
                ret += item + " ";
            }
            ret += '\n';
        }
        if(__in!= null && __in.size()>0) {
            ret += "In: ";
            for (String item : __in) {
                ret += item + " ";
            }
            ret += '\n';
        }

        return ret;
    }

}
