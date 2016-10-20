package DataFlow;

import CFGBuilder.BasicBlock;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 10/19/16.
 */
abstract public class DataFlowNode extends BasicBlock{
    protected List<String> __gen;
    protected List<String> __kill;
    protected List<String> __out;
    protected List<String> __in;

    public DataFlowNode(BasicBlock bb) {
        super(bb);
        __gen = new ArrayList<String>();
        __kill = new ArrayList<String>();
    }

    public List<String> getGen() { return __gen; }
    public List<String> getKill() {return __kill; }

}
