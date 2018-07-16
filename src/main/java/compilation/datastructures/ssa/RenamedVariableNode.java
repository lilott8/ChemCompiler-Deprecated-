package compilation.datastructures.ssa;


import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 4/25/17.
 */
/*
 * This is used to resolve the issue within the rename variable algorithm. When a sigma node is placed it creates
 * multiple output symbols. This skews the renamed stack and the subsequent search cannot determine which version is
 * supposed to be used. This node flattens the outputs to take single spot on stack. Get variable will choose which
 * symbol to use.
 */
public class RenamedVariableNode {
    private List<String> renamedNodes = new ArrayList<>();
    private Integer originID;
    private Integer popCount;

    public RenamedVariableNode(List<String> nodes, Integer id) {
        this.renamedNodes.addAll(nodes);
        this.originID = id;
        this.popCount = 0;
    }

    public RenamedVariableNode(String node, Integer id) {
        this.renamedNodes = new ArrayList<>();
        this.renamedNodes.add(node);
        this.originID = id;
        this.popCount = 0;

    }

    public Integer getOriginID() {
        return originID;
    }

    public Integer size() {
        return renamedNodes.size();
    }

    public String getVariable(Integer numSuccessor) {
        if (numSuccessor == -1)
            return this.renamedNodes.get(0);
        if (renamedNodes.size() > 1 && numSuccessor < renamedNodes.size())
            return this.renamedNodes.get(numSuccessor);
        return this.renamedNodes.get(0);
    }

    public Boolean canPop() {
        return ++popCount > renamedNodes.size();
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("id: ").append(originID).append("\t").append(this.renamedNodes);

        return sb.toString();
    }
}
