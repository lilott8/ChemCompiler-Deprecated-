package CompilerDataStructures.StaticSingleAssignment;


import java.util.ArrayList;

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
    private ArrayList<String> __renamedNodes;
    private Integer __originID;
    private Integer __popCount;

    public RenamedVariableNode( ArrayList<String> nodes, Integer id){
        this.__renamedNodes = nodes;
        this.__originID = id;
        this.__popCount = 0;
    }
    public RenamedVariableNode( String node, Integer id){
        this.__renamedNodes = new ArrayList<String>();
        this.__renamedNodes.add(node);
        this.__originID = id;
        this.__popCount = 0;

    }
    public Integer getOrginID() {return __originID; }

    public Integer size() { return __renamedNodes.size(); }

    public String GetVariable(Integer NumSuccessor){
        if(NumSuccessor == -1 )
            return this.__renamedNodes.get(0);
        if(__renamedNodes.size() > 1 && NumSuccessor < __renamedNodes.size())
            return this.__renamedNodes.get(NumSuccessor);
        return this.__renamedNodes.get(0);
    }

    public Boolean CanPop(){
        return ++__popCount > __renamedNodes.size();
    }
}
