package Translators.MFSimSSA;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.InstructionEdge;
import CompilerDataStructures.InstructionNode;
import CompilerDataStructures.StaticSingleAssignment.PHIInstruction;
import CompilerDataStructures.StaticSingleAssignment.RenamedVariableNode;
import CompilerDataStructures.StaticSingleInformation.SigmaInstruction;
import Translators.MFSimSSA.OperationNode.MFSimSSACool;
import Translators.MFSimSSA.OperationNode.MFSimSSADetect;
import Translators.MFSimSSA.OperationNode.MFSimSSADispense;
import Translators.MFSimSSA.OperationNode.MFSimSSAHeat;
import Translators.MFSimSSA.OperationNode.MFSimSSAMix;
import Translators.MFSimSSA.OperationNode.MFSimSSANode;
import Translators.MFSimSSA.OperationNode.MFSimSSAOutput;
import Translators.MFSimSSA.OperationNode.MFSimSSASplit;
import Translators.MFSimSSA.OperationNode.MFSimSSAStorage;
import Translators.MFSimSSA.OperationNode.MFSimSSATransferIn;
import Translators.MFSimSSA.OperationNode.MFSimSSATransferOut;
import executable.instructions.Combine;
import executable.instructions.Detect;
import executable.instructions.Heat;
import executable.instructions.Instruction;
import executable.instructions.Output;
import executable.instructions.React;
import executable.instructions.Split;
import executable.instructions.Store;
import substance.Chemical;
import variable.Instance;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADAG {
    private static final Logger logger = LogManager.getLogger(MFSimSSADAG.class);
    private MFSimSSATranslator.IDGen __uniqueIDGen;
    private String __name;
    private Map<Integer, MFSimSSANode> __nodes;
    private Map<Integer, ArrayList<MFSimSSATransferOut> > __transOut;
    private Map<Integer, ArrayList<MFSimSSATransferIn>> __transIn;
    private List<MFSimSSADispense> __dispense;

    public MFSimSSADAG(BasicBlock bb, MFSimSSATranslator.IDGen parentsIDGen, HashMap<String, Stack<RenamedVariableNode>> variableStack){
        __uniqueIDGen = parentsIDGen;
        __name = "DAG" + bb.ID().toString();
        __nodes = new LinkedHashMap <Integer, MFSimSSANode>();
        __transOut = new HashMap <Integer, ArrayList<MFSimSSATransferOut>>();
        __transIn = new HashMap <Integer, ArrayList<MFSimSSATransferIn>>();
        __dispense = new ArrayList<MFSimSSADispense>();

        for(String transferInDroplet: bb.getBasicBlockEntryTable().keySet()){
            if(bb.getSymbolTable().contains(transferInDroplet) && bb.getSymbolTable().get(transferInDroplet).IsStationary())
                continue;

            // set of
            Set<Integer> predecessorSet = bb.getBasicBlockEntryTable().get(transferInDroplet);
            for( Integer predecessorID : predecessorSet) {
                if ( predecessorID != -2 ) {
                    MFSimSSATransferIn transIn = new MFSimSSATransferIn(__uniqueIDGen.getNextID(), transferInDroplet,transferInDroplet);
                    //__nodes.put(predecessorID,transIn);
                    if (__transIn.get(predecessorID) == null) {
                        __transIn.put(predecessorID, new ArrayList<MFSimSSATransferIn>());
                    }
                    __transIn.get(predecessorID).add(transIn);
                    break;
                }
            }
        }


        for (Integer numInstructions = 0; numInstructions < bb.getInstructions().size(); numInstructions++) {
            InstructionNode instructionNode = bb.getInstructions().get(numInstructions);

            if (instructionNode instanceof SigmaInstruction || instructionNode instanceof PHIInstruction) {
                continue;
            }

            if (numInstructions == 0) {
                logger.info("LEADER");
            }
            else {
                //
            }


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
                else if (instruction instanceof Dispense) {
                    Instance input = (Instance)instruction.getInputs().values().toArray()[0];
                    Instance output = (Instance)instruction.getOutputs().values().toArray()[0];
                    n = new MFSimSSADispense(__uniqueIDGen.getNextID(), output.getName(), input.getName(), Math.round(input.getSubstance().getVolume().getQuantity()));
                    //System.out.println();
                }
                else {
                    logger.fatal("Unknown Conversion for: " + instruction.toString());
                    n = null;
                }
            }

            for(String dispense : instructionNode.getDispenseSymbols()){
                if(instructionNode.Instruction().getInputs().get(dispense) instanceof Instance
                        && ((Instance) instructionNode.Instruction().getInputs().get(dispense)).getIsStationary())
                    continue;

                // get dispense amount
                Integer amount = 0;  //template amount
                Boolean changed = false;
                for (String input : instruction.getInputs().keySet()) {
                    if (variableStack.containsKey(input)) {
//                        for (RenamedVariableNode renamedVariableNode : variableStack.get(input)) {
//                            for (Integer i = 0; i < variableStack.get(input).size(); i++) {
//                                if (renamedVariableNode.GetVariable(i).equals(dispense)) {

                                    if (instruction.getInputs().get(input) instanceof Instance) {
                                        if (((Instance) instruction.getInputs().get(input)).getSubstance() instanceof Chemical) {
                                            amount = (int) ((Instance) instruction.getInputs().get(input)).getSubstance().getVolume().getQuantity();
                                            changed = true;
                                        }
                                    }
//                                }
//                            }
//                        }
                    }

                }
                if (!changed) {
                    logger.warn("Setting template volume amount");
                    amount = 999;
                }
                MFSimSSADispense dis = new MFSimSSADispense(this.__uniqueIDGen.getNextID(), dispense, dispense, amount);
                if (n != null)
                    dis.addSuccessor(n.getID());
                __dispense.add(dis);
            }
            if (n != null)
                __nodes.put(instructionNode.ID(),n);


        }

        for (String transferOutDroplet: bb.getBasicBlockExitTable().keySet()) {
            InstructionNode instr = bb.getInstructions().get(bb.getInstructions().size()-1);
            if (instr instanceof SigmaInstruction || instr instanceof PHIInstruction) {
                //continue;
            }
            else if (instr.Instruction().getInputs().containsKey(transferOutDroplet) && instr.Instruction().getInputs().get(transferOutDroplet) instanceof Instance &&
                    ((Instance) instr.Instruction().getInputs().get(transferOutDroplet)).getIsStationary()) {
                continue;
            }
            else if (instr.Instruction() instanceof Output) {
                continue;
            }
            MFSimSSATransferOut transOut = new MFSimSSATransferOut(__uniqueIDGen.getNextID(), transferOutDroplet, transferOutDroplet);
            if (__transOut.get(transOut.getID()) == null) {
                    __transOut.put(transOut.getID(), new ArrayList<MFSimSSATransferOut>());
            }
            __transOut.get(transOut.getID()).add(transOut);
        }


//        Set<Integer> keystoRemove = new HashSet<Integer>();
//        //add successor edges
//        for(Integer toutPredKey : this.__transOut.keySet()){
//            if(__nodes.containsKey(toutPredKey)) {
//                __nodes.get(toutPredKey).addSuccessor(toutPredKey);
//            }
//            else if(__transIn.containsKey(toutPredKey)){
//                //__transIn.get(toutPredKey).get(toutPredKey);
//            }
//            else{
//                //remove edge
//                keystoRemove.add(toutPredKey);
////                this.__transOut.remove(toutPredKey);
//            }
//        }
//
//        for(Integer key: keystoRemove)
//            this.__transOut.remove(key);


        for(InstructionEdge edge: bb.getEdges()){
            if(__nodes.containsKey(edge.getDestination())){//I am a child of
                Integer destination =__nodes.get(edge.getDestination()).getID();
                if(__nodes.containsKey(edge.getSource())) { //another node
                    MFSimSSANode node = __nodes.get(edge.getSource());
                    if(node.getID() < destination)
                        node.addSuccessor(destination);
                }
                else if(__transIn.containsKey(edge.getSource())){
                    MFSimSSATransferIn node = __transIn.get(edge.getSource()).get(destination);
                    if(node.getID() < destination )
                        node.addSuccessor(destination);
                }
            }
        }



        for (ArrayList<MFSimSSATransferIn> transIn : __transIn.values()) {
            for (MFSimSSATransferIn in : transIn) {
                if (__nodes.size() > 0) {
                    for (InstructionNode instruction : bb.getInstructions()) {
                        if (instruction.ID() < 0)
                            continue;
                        in.addSuccessor(__nodes.get(instruction.ID()).getID());
                        break;
                    }
                    //in.addSuccessor(__nodes.get(bb.getInstructions().get(0).ID()).getID());
                }
                else {
                    Integer succ = 0;
                    for (Integer transOut : __transOut.keySet()) {
                        succ = transOut;
                        break;
                    }
                    in.addSuccessor(succ);
                }
            }
        }

        for (ArrayList<MFSimSSATransferOut> transOut : __transOut.values()) {
            for (MFSimSSATransferOut out : transOut) {
                if (__nodes.size() > 0) {
                    for (Integer instrIndex = bb.getInstructions().size()-1; ; --instrIndex) {
                        InstructionNode instruction = bb.getInstructions().get(instrIndex);
                        if (instruction.ID() > 0) {
                            __nodes.get(instruction.ID()).addSuccessor(out.getID());
                            break;
                        }
                    }
                }
                else {
                   // do nothing, transIn should take care of the edge between the two
                }
            }
        }

    }

    public Map<Integer, MFSimSSANode> getNodes() { return __nodes; }

    public Map<Integer, ArrayList<MFSimSSATransferOut>> getTransferOutNode() { return __transOut; }

    public Map<Integer, ArrayList<MFSimSSATransferIn>> getTransferInNode() { return __transIn; }
    public String getName() { return this.__name; }

    public String toString(){
        String ret = "DagName (" + this.__name + ")\n";
        for(ArrayList<MFSimSSATransferIn> tin : this.__transIn.values()){
            for (MFSimSSATransferIn ttin : tin) {
                ret += ttin.toString() + "\n";
            }
        }
        for(MFSimSSADispense disp : this.__dispense){
            ret += disp.toString() + "\n";
        }

        for(MFSimSSANode n : __nodes.values()) {
            ret += n.toString() + "\n";
        }

        for(ArrayList<MFSimSSATransferOut> tout : this.__transOut.values()){
            for (MFSimSSATransferOut ttout : tout) {
                ret += ttout.toString() + "\n";
            }
        }
        return ret;
    }

}