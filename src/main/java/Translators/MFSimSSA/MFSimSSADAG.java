package Translators.MFSimSSA;

import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.InstructionNode;
import Translators.MFSimSSA.OperationNode.*;
import executable.instructions.*;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADAG {
    private static final Logger logger = LogManager.getLogger(MFSimSSADAG.class);
    private Integer __uniqueIDGen;
    private String __name;
    private Map<MFSimSSANode,Integer> __nodes;

    public MFSimSSADAG(BasicBlock bb, Integer parentsIDGen){
        __uniqueIDGen = parentsIDGen;
        __name = "DAG" + bb.ID().toString();
        __nodes = new HashMap <MFSimSSANode, Integer>();

        for(String transferInDroplet: bb.getBasicBlockEntryTable().keySet()){
            Set<Integer> predecessorSet = bb.getBasicBlockEntryTable().get(transferInDroplet);
            for( Integer predecessorID : predecessorSet) {
                if ( predecessorID != -2 ) {
                    __nodes.put(new MFSimSSATransferIn(__uniqueIDGen++, transferInDroplet),predecessorID);
                }
            }
        }
        for(InstructionNode instructionNode : bb.getInstructions()){
            MFSimSSANode n;
            Instruction instruction = instructionNode.Instruction();

            if(instruction instanceof Combine)
                n = new MFSimSSAMix(__uniqueIDGen++,(Combine)instruction);
            else if (instruction instanceof Detect)
                n = new MFSimSSADetect(__uniqueIDGen++,(Detect)instruction);
            else if (instruction instanceof Heat)
                n = new MFSimSSAHeat(__uniqueIDGen++,(Heat)instruction);
            else if (instruction instanceof Split)
                n = new MFSimSSASplit(__uniqueIDGen++,(Split)instruction);
            else if (instruction instanceof Store)
                n = new MFSimSSAStorage(__uniqueIDGen++,(Store)instruction);
            else if (instruction instanceof Output)
                n = new MFSimSSAOutput(__uniqueIDGen++,(Output)instruction);
            else
                n = null;


            for(String dispense : instructionNode.getDispenseSymbols()){
                logger.warn("Setting template volume amount");
                MFSimSSADispense dis = new MFSimSSADispense(this.__uniqueIDGen++, dispense, dispense, 10);
                if (n != null)
                    dis.addSuccessor(n.getID());
                __nodes.put(dis,-2);
            }
            __nodes.put(n,instructionNode.ID());


        }
        for(String transferOutDroplet: bb.getBasicBlockExitTable().keySet()) {
            for( Integer out : bb.getBasicBlockExitTable().get(transferOutDroplet))
            __nodes.put(new MFSimSSATransferIn(__uniqueIDGen++, transferOutDroplet),out);
        }


        //add successor edges
    }

    public String getName() { return this.__name; }

    public String toString(){
        String ret = "DagName (" + this.__name + ")\n";
        for(MFSimSSANode n : __nodes.keySet())
            ret += n.toString() + "\n";

        return ret;
    }
}