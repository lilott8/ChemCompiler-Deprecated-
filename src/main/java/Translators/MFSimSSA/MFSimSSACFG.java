package Translators.MFSimSSA;

import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.BasicBlockEdge;
import ControlFlowGraph.CFG;
import Translators.MFSimSSA.OperationNode.MFSimSSATransferIn;
import Translators.MFSimSSA.OperationNode.MFSimSSATransferOut;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSACFG{
    private static final Logger logger = LogManager.getLogger(MFSimSSACFG.class);

    private MFSimSSATranslator.IDGen __uniqueIDGen;
    private HashMap<Integer, MFSimSSADAG> __dags;

    private HashMap<Integer, List<BasicBlockEdge>> __conditionalGroups;

    public MFSimSSACFG(CFG controlFlowGraph, MFSimSSATranslator.IDGen uniqueID){
        __uniqueIDGen = uniqueID;
        __dags = new HashMap<Integer, MFSimSSADAG>();
        __conditionalGroups = new HashMap<Integer, List<BasicBlockEdge>>();

        for(BasicBlock bb : controlFlowGraph.getBasicBlocks()){
            MFSimSSADAG dag = new MFSimSSADAG(bb, uniqueID);
            __dags.put(bb.ID(),dag);
            logger.info(dag);
        }
        for(BasicBlockEdge edge: controlFlowGraph.getBasicBlockEdges()){
            List<BasicBlockEdge> conditionalGroup;
            if(__conditionalGroups.containsKey(edge.getSource())){
                conditionalGroup= __conditionalGroups.get(edge.getSource());

            }
            else {
                conditionalGroup = new ArrayList<BasicBlockEdge>();
            }
            conditionalGroup.add(edge);
            __conditionalGroups.put(edge.getSource(),conditionalGroup);
        }
    }

    public String toString(String filename){
        String ret=  "NAME(" + filename + ")\n\n";

        for(MFSimSSADAG dag: __dags.values()){
            ret += "DAG("+ dag.getName() + ")\n";
        }
        ret += "\n";

        ret+= "NUMCG(" + __conditionalGroups.size() + ")\n\n";

        int controlGroup = 0;
        for(Integer sourceBasicBlockID : __conditionalGroups.keySet()){
            MFSimSSADAG sourceBasicBlock = __dags.get(sourceBasicBlockID);
            for(BasicBlockEdge edge : __conditionalGroups.get(sourceBasicBlockID)){
                MFSimSSADAG destinationBasicBlock = __dags.get(edge.getDestination());
                if(edge.getCondition() == "UNCONDITIONAL")
                    ret+="COND("+ controlGroup + ", 1, " + sourceBasicBlock.getName() + ", " + destinationBasicBlock.getName() + ", -1)\n";
                else {
                    String conditionalExpression = resolveExpression(edge.getCondition());
                    ret += "COND("+ controlGroup + ", 1, " + sourceBasicBlock.getName() + ", " + destinationBasicBlock.getName() + ", " + conditionalExpression;
                }
                ret+="\n";
                for(MFSimSSATransferOut transferOut: sourceBasicBlock.getTransferOutNode().values()){
                    for(MFSimSSATransferIn transferIn: destinationBasicBlock.getTransferInNode().values()){
                        if(transferOut.getTransferedSymbol().equals(transferIn.getTransferedSymbol())){
                            ret +="TD("+ sourceBasicBlock.getName() + ", " + transferOut.getID() + ", " + destinationBasicBlock.getName()+", " + transferIn.getID() +")\n";
                        }
                    }
                }
            }

            controlGroup++;
            ret +="\n\n";
        }

        return ret;
    }

    private String resolveExpression(String s){
        Integer expressionID = this.__uniqueIDGen.getNextID();
        String ret =  expressionID + ")\nEXP("+ expressionID +"<INSERT CONDITION HERE>)\n";

        return ret;

    }
}