package compilation.dataflow;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.InstructionNode;

/**
 * Created by chriscurtis on 10/19/16.
 */
abstract public class DataFlowNode {
    protected Integer id;
    protected Set<String> gen;
    protected Set<String> kill;
    protected List<String> out;
    protected List<String> in;

    public DataFlowNode(Integer id){
        this.id = id;
        gen = null;
        kill = null;
        in = new ArrayList<>();
        out = new ArrayList<>();
    }
    public DataFlowNode(BasicBlock bb) {
        gen = new HashSet<>();
        kill = new HashSet<>();
        in = new ArrayList<>();
        out = new ArrayList<>();
        id = bb.ID();

        for(InstructionNode i :bb.getInstructions()) {
            gen.addAll(i.getInstruction().getOutputs().keySet());
        }



    }
    public String toString() {
        String ret = "";
        if(gen != null && gen.size()>0) {
            ret += "Gen: ";
            for (String item : gen) {
                ret += item + " ";
            }
            ret += '\n';
        }
        if(kill != null && kill.size()>0) {
            ret += "Kill: ";
            for (String item : kill) {
                ret += item + " ";
            }
            ret += '\n';
        }
        if(out != null && out.size()>0) {
            ret += "Out: ";
            for (String item : out) {
                ret += item + " ";
            }
            ret += '\n';
        }
        if(in != null && in.size()>0) {
            ret += "In: ";
            for (String item : in) {
                ret += item + " ";
            }
            ret += '\n';
        }

        return ret;
    }

}
