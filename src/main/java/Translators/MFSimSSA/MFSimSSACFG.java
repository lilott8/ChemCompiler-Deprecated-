package Translators.MFSimSSA;

import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.BasicBlockEdge;
import ControlFlowGraph.CFG;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSACFG{
    private Integer __uniqueIDGen;
    private HashMap<Integer, MFSimSSADAG> __dags;

    private HashMap<Integer, List<BasicBlockEdge>> _conditionalGroups;

    public MFSimSSACFG(CFG controlFlowGraph, Integer uniqueID){
        __uniqueIDGen = uniqueID;
        __dags = new HashMap<Integer, MFSimSSADAG>();
        _conditionalGroups = new HashMap<Integer, List<BasicBlockEdge>>();
        for(BasicBlock bb : controlFlowGraph.getBasicBlocks()){
            __dags.put(bb.ID(), new MFSimSSADAG(bb, this.__uniqueIDGen++));
        }
    }

    public String toString(String filename){
        String ret=  "NAME(" + filename + ")\n\n";

        for(MFSimSSADAG dag: __dags.values()){
            ret += "DAG("+ dag.getName() + ")\n";
        }
        ret += "\n";

        ret+= "NUMCG()";

        return ret;
    }
}