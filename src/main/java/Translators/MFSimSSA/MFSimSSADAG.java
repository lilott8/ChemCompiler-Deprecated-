package Translators.MFSimSSA;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.InstructionEdge;
import CompilerDataStructures.InstructionNode;
import Translators.MFSimSSA.OperationNode.*;
import executable.instructions.*;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import variable.Instance;

import java.util.*;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADAG {
    private static final Logger logger = LogManager.getLogger(MFSimSSADAG.class);
    private MFSimSSATranslator.IDGen __uniqueIDGen;
    private String __name;
    private Map<Integer, MFSimSSANode> __nodes;
    private Map<Integer, MFSimSSATransferOut> __transOut;
    private Map<Integer, MFSimSSATransferIn> __transIn;
    private List<MFSimSSADispense> __dispense;

    public MFSimSSADAG(BasicBlock bb, MFSimSSATranslator.IDGen parentsIDGen){
        __uniqueIDGen = parentsIDGen;
        __name = "DAG" + bb.ID().toString();
        __nodes = new LinkedHashMap <Integer, MFSimSSANode>();
        __transOut = new HashMap <Integer,MFSimSSATransferOut>();
        __transIn = new HashMap <Integer,MFSimSSATransferIn>();
        __dispense = new ArrayList<MFSimSSADispense>();

        for(String transferInDroplet: bb.getBasicBlockEntryTable().keySet()){
            if(bb.getSymbolTable().contains(transferInDroplet) && bb.getSymbolTable().get(transferInDroplet).IsStationary())
                continue;
            Set<Integer> predecessorSet = bb.getBasicBlockEntryTable().get(transferInDroplet);
            for( Integer predecessorID : predecessorSet) {
                if ( predecessorID != -2 ) {
                    MFSimSSATransferIn transIn = new MFSimSSATransferIn(__uniqueIDGen.getNextID(), transferInDroplet,transferInDroplet);
                    //__nodes.put(predecessorID,transIn);
                    __transIn.put(predecessorID,transIn);
                    break;
                }
            }
        }


        for(InstructionNode instructionNode : bb.getInstructions()){
            MFSimSSANode n = null;

            Instruction instruction = instructionNode.Instruction();

            if (instruction != null) {
                if (instruction instanceof Combine)
                    n = new MFSimSSAMix(__uniqueIDGen.getNextID(), (Combine) instruction);
                else if (instruction instanceof Detect)
                    n = new MFSimSSADetect(__uniqueIDGen.getNextID(), (Detect) instruction);
                else if (instruction instanceof Heat)
                    n = new MFSimSSAHeat(__uniqueIDGen.getNextID(), (Heat) instruction);
                else if (instruction instanceof Split)
                    n = new MFSimSSASplit(__uniqueIDGen.getNextID(), (Split) instruction);
                else if (instruction instanceof Store)
                    n = new MFSimSSAStorage(__uniqueIDGen.getNextID(), (Store) instruction);
                else if (instruction instanceof Output)
                    n = new MFSimSSAOutput(__uniqueIDGen.getNextID(), (Output) instruction);
                else if (instruction instanceof React)
                    n = new MFSimSSACool(__uniqueIDGen.getNextID(), (React) instruction);
                else {
                    logger.fatal("Unknown Conversion for: " + instruction.toString());
                    n = null;
                }
            }

            for(String dispense : instructionNode.getDispenseSymbols()){
                if(instructionNode.Instruction().getInputs().get(dispense) instanceof Instance
                        && ((Instance) instructionNode.Instruction().getInputs().get(dispense)).getIsStationary())
                    continue;


                logger.warn("Setting template volume amount");
                // get ammount:
                MFSimSSADispense dis = new MFSimSSADispense(this.__uniqueIDGen.getNextID(), dispense, dispense, 10);
                if (n != null)
                    dis.addSuccessor(n.getID());
//                __nodes.put((dis.getID()*-1), dis);
                __dispense.add(dis);
            }
            if (n != null)
                __nodes.put(instructionNode.ID(),n);


        }
        for(String transferOutDroplet: bb.getBasicBlockExitTable().keySet()) {
            if(bb.getSymbolTable().contains(transferOutDroplet) && bb.getSymbolTable().get(transferOutDroplet).IsStationary())
                continue;
            for( Integer out : bb.getBasicBlockExitTable().get(transferOutDroplet)) {
                MFSimSSATransferOut transOut = new MFSimSSATransferOut(__uniqueIDGen.getNextID(), transferOutDroplet, transferOutDroplet);
                //__nodes.put(out, transOut);
                __transOut.put(out,transOut);
            }
        }


        Set<Integer> keystoRemove = new HashSet<Integer>();
        //add successor edges
        for(Integer toutPredKey : this.__transOut.keySet()){
            if(__nodes.containsKey(toutPredKey)) {
                __nodes.get(toutPredKey).addSuccessor(this.__transOut.get(toutPredKey).getID());
            }
            else if(__transIn.containsKey(toutPredKey)){
                __transIn.get(toutPredKey).addSuccessor(this.__transOut.get(toutPredKey).getID());
            }
            else{
                //remove edge
                keystoRemove.add(toutPredKey);
//                this.__transOut.remove(toutPredKey);
            }
        }

        for(Integer key: keystoRemove)
            this.__transOut.remove(key);


        for(InstructionEdge edge: bb.getEdges()){
            if(__nodes.containsKey(edge.getDestination())){//I am a child of
                Integer destination =__nodes.get(edge.getDestination()).getID();
                if(__nodes.containsKey(edge.getSource())) { //another node
                    MFSimSSANode node = __nodes.get(edge.getSource());
                    if(node.getID() < destination)
                        node.addSuccessor(destination);
                }
                else if(__transIn.containsKey(edge.getSource())){
                    MFSimSSATransferIn node = __transIn.get(edge.getSource());
                    if(node.getID() < destination )
                        node.addSuccessor(destination);
                }
            }
        }
    }

    public Map<Integer, MFSimSSATransferOut> getTransferOutNode() { return __transOut; }

    public Map<Integer, MFSimSSATransferIn> getTransferInNode() { return __transIn; }
    public String getName() { return this.__name; }

    public String toString(){
        String ret = "DagName (" + this.__name + ")\n";
        for(MFSimSSATransferIn tin : this.__transIn.values()){
            ret += tin.toString() + "\n";
        }
        for(MFSimSSADispense disp : this.__dispense){
            ret += disp.toString() + "\n";
        }

        for(MFSimSSANode n : __nodes.values()) {
            ret += n.toString() + "\n";
        }

        for(MFSimSSATransferOut tout : this.__transOut.values()){
            ret += tout.toString() + "\n";
        }
        return ret;
    }

}