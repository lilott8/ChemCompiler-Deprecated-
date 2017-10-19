package translators.mfsim;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import compilation.datastructures.InstructionEdge;
import compilation.datastructures.InstructionNode;
import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.ssa.PHIInstruction;
import compilation.datastructures.ssa.RenamedVariableNode;
import compilation.datastructures.ssi.SigmaInstruction;
import executable.instructions.Combine;
import executable.instructions.Detect;
import executable.instructions.Dispense;
import executable.instructions.Heat;
import executable.instructions.Instruction;
import executable.instructions.Output;
import executable.instructions.React;
import executable.instructions.Split;
import executable.instructions.Store;
import substance.Chemical;
import translators.mfsim.operationnode.MFSimSSACool;
import translators.mfsim.operationnode.MFSimSSADetect;
import translators.mfsim.operationnode.MFSimSSADispense;
import translators.mfsim.operationnode.MFSimSSAHeat;
import translators.mfsim.operationnode.MFSimSSAMix;
import translators.mfsim.operationnode.MFSimSSANode;
import translators.mfsim.operationnode.MFSimSSAOutput;
import translators.mfsim.operationnode.MFSimSSASplit;
import translators.mfsim.operationnode.MFSimSSAStorage;
import translators.mfsim.operationnode.MFSimSSATransferIn;
import translators.mfsim.operationnode.MFSimSSATransferOut;
import variable.Instance;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADAG {
    private static final Logger logger = LogManager.getLogger(MFSimSSADAG.class);
    private MFSimSSATranslator.IDGen uniqueIdGen;
    private String name;
    private Map<Integer, MFSimSSANode> node = new HashMap<>();
    private Map<Integer, ArrayList<MFSimSSATransferOut>> transOut = new HashMap<>();
    private Map<Integer, ArrayList<MFSimSSATransferIn>> transIn = new HashMap<>();
    private List<MFSimSSADispense> dispense = new ArrayList<>();

    public MFSimSSADAG(BasicBlock bb, MFSimSSATranslator.IDGen parentsIDGen, Map<String, Stack<RenamedVariableNode>> variableStack){
        uniqueIdGen = parentsIDGen;
        name = "DAG" + bb.ID().toString();

        for(String transferInDroplet: bb.getBasicBlockEntryTable().keySet()){
            if(bb.getSymbolTable().contains(transferInDroplet) && bb.getSymbolTable().get(transferInDroplet).IsStationary())
                continue;

            // set of
            Set<Integer> predecessorSet = bb.getBasicBlockEntryTable().get(transferInDroplet);
            for( Integer predecessorID : predecessorSet) {
                if ( predecessorID != -2 ) {
                    MFSimSSATransferIn transIn = new MFSimSSATransferIn(uniqueIdGen.getNextID(), transferInDroplet, transferInDroplet);
                    //nodes.put(predecessorID,transIn);
                    if (this.transIn.get(predecessorID) == null) {
                        this.transIn.put(predecessorID, new ArrayList<MFSimSSATransferIn>());
                    }
                    this.transIn.get(predecessorID).add(transIn);
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
            MFSimSSANode n = null;
            Instruction instruction = instructionNode.getInstruction();
            if (instruction != null) {
                if (instruction instanceof Combine) {
                    n = new MFSimSSAMix(uniqueIdGen.getNextID(), (Combine) instruction);
                } else if (instruction instanceof Detect) {
                    n = new MFSimSSADetect(uniqueIdGen.getNextID(), (Detect) instruction);
                } else if (instruction instanceof Heat) {
                    n = new MFSimSSAHeat(uniqueIdGen.getNextID(), (Heat) instruction);
                } else if (instruction instanceof Split) {
                    n = new MFSimSSASplit(uniqueIdGen.getNextID(), (Split) instruction);
                } else if (instruction instanceof Store) {
                    n = new MFSimSSAStorage(uniqueIdGen.getNextID(), (Store) instruction);
                } else if (instruction instanceof Output) {
                    n = new MFSimSSAOutput(uniqueIdGen.getNextID(), (Output) instruction);
                } else if (instruction instanceof React) {
                    n = new MFSimSSACool(uniqueIdGen.getNextID(), (React) instruction);
                }
                else if (instruction instanceof Dispense) {
                    Instance input = (Instance)instruction.getInputs().values().toArray()[0];
                    Instance output = (Instance)instruction.getOutputs().values().toArray()[0];
                    n = new MFSimSSADispense(uniqueIdGen.getNextID(), output.getName(), input.getName(), Math.round(input.getSubstance().getVolume().getQuantity()));
                }
                else {
                    logger.fatal("Unknown Conversion for: " + instruction.toString());
                    n = null;
                }
            }

            for(String dispense : instructionNode.getDispenseSymbols()){
                if(instructionNode.getInstruction().getInputs().get(dispense) instanceof Instance
                        && ((Instance) instructionNode.getInstruction().getInputs().get(dispense)).getIsStationary())
                    continue;

                // get dispense amount
                Integer amount = 0;  //template amount
                Boolean changed = false;
                for (String input : instruction.getInputs().keySet()) {
                    if (variableStack.containsKey(input)) {
                                    if (instruction.getInputs().get(input) instanceof Instance) {
                                        if (((Instance) instruction.getInputs().get(input)).getSubstance() instanceof Chemical) {
                                            amount = (int) ((Instance) instruction.getInputs().get(input)).getSubstance().getVolume().getQuantity();
                                            changed = true;
                                        }
                                    }
                    }

                }
                if (!changed) {
                    logger.warn("Setting template volume amount");
                    amount = 999;
                }
                MFSimSSADispense dis = new MFSimSSADispense(this.uniqueIdGen.getNextID(), dispense, dispense, amount);
                if (n != null)
                    dis.addSuccessor(n.getID());
                this.dispense.add(dis);
            }
            if (n != null)
                node.put(instructionNode.getId(), n);


        }

        for (String transferOutDroplet: bb.getBasicBlockExitTable().keySet()) {
            InstructionNode instr = bb.getInstructions().get(bb.getInstructions().size()-1);
            if (instr instanceof SigmaInstruction || instr instanceof PHIInstruction) {
                //continue;
            }
            else if (instr.getInstruction().getInputs().containsKey(transferOutDroplet) && instr.getInstruction().getInputs().get(transferOutDroplet) instanceof Instance &&
                    ((Instance) instr.getInstruction().getInputs().get(transferOutDroplet)).getIsStationary()) {
                continue;
            }
            else if (instr.getInstruction() instanceof Output) {
                continue;
            }
            MFSimSSATransferOut transOut = new MFSimSSATransferOut(uniqueIdGen.getNextID(), transferOutDroplet, transferOutDroplet);
            if (this.transOut.get(transOut.getID()) == null) {
                this.transOut.put(transOut.getID(), new ArrayList<MFSimSSATransferOut>());
            }
            this.transOut.get(transOut.getID()).add(transOut);
        }

        for(InstructionEdge edge: bb.getEdges()){
            if (node.containsKey(edge.getDestination())) {//I am a child of
                Integer destination = node.get(edge.getDestination()).getID();
                if (node.containsKey(edge.getSource())) { //another node
                    MFSimSSANode node = this.node.get(edge.getSource());
                    if(node.getID() < destination)
                        node.addSuccessor(destination);
                } else if (transIn.containsKey(edge.getSource())) {
                    MFSimSSATransferIn node = transIn.get(edge.getSource()).get(destination);
                    if(node.getID() < destination )
                        node.addSuccessor(destination);
                }
            }
        }
        for (ArrayList<MFSimSSATransferIn> transIn : transIn.values()) {
            for (MFSimSSATransferIn in : transIn) {
                if (node.size() > 0) {
                    for (InstructionNode instruction : bb.getInstructions()) {
                        if (instruction.getId() < 0)
                            continue;
                        in.addSuccessor(node.get(instruction.getId()).getID());
                        break;
                    }
                    //in.addSuccessor(nodes.get(bb.getInstructions().get(0).getId()).getID());
                }
                else {
                    Integer succ = 0;
                    for (Integer transOut : transOut.keySet()) {
                        succ = transOut;
                        break;
                    }
                    in.addSuccessor(succ);
                }
            }
        }

        for (ArrayList<MFSimSSATransferOut> transOut : transOut.values()) {
            for (MFSimSSATransferOut out : transOut) {
                if (node.size() > 0) {
                    for (Integer instrIndex = bb.getInstructions().size()-1; ; --instrIndex) {
                        InstructionNode instruction = bb.getInstructions().get(instrIndex);
                        if (instruction.getId() > 0) {
                            node.get(instruction.getId()).addSuccessor(out.getID());
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

    public Map<Integer, MFSimSSANode> getNodes() {
        return node;
    }

    public Map<Integer, ArrayList<MFSimSSATransferOut>> getTransferOutNode() {
        return transOut;
    }

    public Map<Integer, ArrayList<MFSimSSATransferIn>> getTransferInNode() {
        return transIn;
    }

    public String getName() {
        return this.name;
    }

    public String toString(){
        String ret = "DagName (" + this.name + ")\n";
        for (ArrayList<MFSimSSATransferIn> tin : this.transIn.values()) {
            for (MFSimSSATransferIn ttin : tin) {
                ret += ttin.toString() + "\n";
            }
        }
        for (MFSimSSADispense disp : this.dispense) {
            ret += disp.toString() + "\n";
        }

        for (MFSimSSANode n : node.values()) {
            ret += n.toString() + "\n";
        }

        for (ArrayList<MFSimSSATransferOut> tout : this.transOut.values()) {
            for (MFSimSSATransferOut ttout : tout) {
                ret += ttout.toString() + "\n";
            }
        }
        return ret;
    }

}