package translators.mfsim;

import compilation.datastructures.basicblock.DependencySlicedBasicBlock;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;

import compilation.datastructures.InstructionEdge;
import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.node.InstructionNode;
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
import translators.mfsim.operationnode.*;
import variable.Instance;
import variable.Variable;

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

    public MFSimSSADAG(BasicBlock bb, MFSimSSATranslator.IDGen parentsIDGen, Map<String, Stack<RenamedVariableNode>> variableStack) {
        uniqueIdGen = parentsIDGen;
        name = "DAG" + bb.getId().toString();

        for (String transferInDroplet : bb.getBasicBlockEntryTable().keySet()) {
            if (bb.getSymbolTable().contains(transferInDroplet) && bb.getSymbolTable().get(transferInDroplet).IsStationary())
                continue;

            // set of
            Set<Integer> predecessorSet = bb.getBasicBlockEntryTable().get(transferInDroplet);
            for (Integer predecessorID : predecessorSet) {
                if (predecessorID != -2) {
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

        // id, def
        // if def is never used, drain
        HashSet<InstructionNode> needToDrain = new HashSet<>();

        for (Integer numInstructions = 0; numInstructions < bb.getInstructions().size(); numInstructions++) {
            InstructionNode instructionNode = bb.getInstructions().get(numInstructions);

            if (instructionNode instanceof SigmaInstruction || instructionNode instanceof PHIInstruction) {
                continue;
            }

            if (numInstructions == 0) {
                // logger.info("LEADER");
            }
            MFSimSSANode n = null;
            Instruction instruction = instructionNode.getInstruction();
            if (instruction != null) {
                boolean stationaryInput = false;
                for (Variable v : instruction.getInputs().values()) {
                    if (v instanceof Instance && ((Instance) v).getIsStationary()) {
                        stationaryInput = true;
                        n = new MFSimSSAReact(uniqueIdGen.getNextID(), instruction, (Instance) v);
                        break;
                    }
                }
                if (stationaryInput) {
                    // already created
                } else if (instruction instanceof Combine) {
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
                    //n = new MFSimSSAReact(uniqueIdGen.getNextID(), (React) instruction);
                    //n = new MFSimSSAHeat(uniqueIdGen.getNextID(), (React) instruction);
                    //n = new MFSimSSACool(uniqueIdGen.getNextID(), (React) instruction);
                } else if (instruction instanceof Dispense) {
                    //Instance input = (Instance) instruction.getInputs().values().toArray()[0];
                    //Instance output = (Instance) instruction.getOutputs().values().toArray()[0];
                    //n = new MFSimSSADispense(uniqueIdGen.getNextID(), output.getName(), input.getName(), Math.round(input.getSubstance().getVolume().getQuantity()));
                    //this.dispense.add((MFSimSSADispense)n);
                    //continue;
                    n = null;
                } else {
                    logger.fatal("Unknown Conversion for: " + instruction.toString());
                    n = null;
                }
            }

            for (String dispense : instructionNode.getDispenseSymbols()) {
//                boolean dontDispense = false;
//                boolean stationary = false;
                if (instructionNode.getInstruction().getInputs().get(dispense) instanceof Instance
                        && ((Instance) instructionNode.getInstruction().getInputs().get(dispense)).getIsStationary()) {
                    continue;
//                    stationary = true;
//                    if (!(instructionNode.getInstruction() instanceof Combine)
//                            && !(instructionNode.getInstruction() instanceof Output)
//                            && !(instructionNode.getInstruction() instanceof Heat))
//                        dontDispense = true;
                }

                // get dispense amount
                Integer amount = 0;  //template amount
                Boolean changed = false;
                for (String input : instruction.getInputs().keySet()) {
                    if (input.equals(dispense)) {
                        if (variableStack.containsKey(input)) {
                            if (instruction.getInputs().get(input) instanceof Instance) {
                                if (((Instance) instruction.getInputs().get(input)).getSubstance() instanceof Chemical) {
                                    if (((Instance) instruction.getInputs().get(input)).getSubstance().getVolume() == null) {
                                        amount = 10;
                                    } else {
                                        amount = (int) ((Instance) instruction.getInputs().get(input)).getSubstance().getVolume().getQuantity();
                                    }
                                    changed = true;
                                }
                            }
                        }
                    }
                }
                if (!changed) {
                    amount = 10;
                }
//                if (dontDispense)
//                    continue;
                MFSimSSADispense dis = new MFSimSSADispense(this.uniqueIdGen.getNextID(), dispense, dispense, amount);
                if (n != null) {
//                    boolean already = false;
//                    if (stationary) {
//                        for (MFSimSSADispense d : this.dispense) {
//                            if (d.getName().equals(dispense)) {
//                                already = true;
//                                dis = d;
//                            }
//                        }
//                    }
//                    if (!already) {
//                        dis.addSuccessor(n.getID());
//                        this.dispense.add(dis);
//                    }
//                    else {
//                        dis.addSuccessor(n.getID());
//                    }
                    dis.addSuccessor(n.getID());
                    this.dispense.add(dis);
                }
                else
                    node.put(instructionNode.getId(), dis);
                //if (n != null)

            }
            if (n != null)
                node.put(instructionNode.getId(), n);

            if (n instanceof MFSimSSAOutput) {
                for (Variable input : instructionNode.getInstruction().getInputs().values()) {
                    if (input instanceof Instance && ((Instance) input).getIsStationary())
                            node.remove(instructionNode.getId());
                }
                continue;
            }

            ArrayList<InstructionEdge> stationaryEdges = new ArrayList<>();
//            for (InstructionEdge edge : bb.getEdges()) {
//                if (edge.getSource().equals(instructionNode.getId()))
//                    stationaryEdges.add(edge);
//            }
            for (InstructionNode succ : instructionNode.getSucc()) {
                if (getInstructionNodeByID(bb, succ.getId()) != null)
                    stationaryEdges.add(new InstructionEdge(instructionNode.getId(), succ.getId()));
            }

            for (InstructionEdge stedge : stationaryEdges) {
            //for (InstructionNode successor : instructionNode.getSucc()) {
                InstructionNode successor = getInstructionNodeByID(bb, stedge.getDestination());
                boolean outputUsed = false;
                boolean isStationary = false;
                boolean inputUsed = false;
                for (String output : instructionNode.getOutputSymbols()) {
                    if (successor.getInputSymbols().contains(output))
                        outputUsed = true;
                }



                for (String input : instructionNode.getInputSymbols()) {
                    if (successor.getInputSymbols().contains(input)) {
                        inputUsed = true;
                    }
                }

                if ((!outputUsed && !inputUsed) || isStationary) {
//                    instructionNode.getSucc().remove(successor);  /* is this doing anything */
//                    ListIterator<InstructionEdge> edgeListIterator = bb.getEdges().listIterator();
//                    while (edgeListIterator.hasNext()) {
//                        InstructionEdge edge = edgeListIterator.next();
//                        if (edge.getSource().equals(instructionNode.getId()) && edge.getDestination().equals(successor.getId())) {
//                            edgeListIterator.remove();
//                            break;
//                        }
//                    }
                    if (!isStationary && (!outputUsed && !inputUsed)) {
                        ListIterator<InstructionEdge> edgeListIterator = bb.getEdges().listIterator();
                        while (edgeListIterator.hasNext()) {
                            InstructionEdge edge = edgeListIterator.next();
                            if (edge.getSource().equals(instructionNode.getId()) && edge.getDestination().equals(successor.getId())) {
                                edgeListIterator.remove();
                                break;
                            }
                        }
                    }
                    needToDrain.add(instructionNode);
                }
            }

            if (instructionNode.getInstruction() != null && instructionNode.getSucc().size() == 0)
                needToDrain.add(instructionNode);

        }

        for (String transferOutDroplet : bb.getBasicBlockExitTable().keySet()) {
            InstructionNode instr = bb.getInstructions().get(bb.getInstructions().size() - 1);
            if (instr instanceof SigmaInstruction || instr instanceof PHIInstruction) {
                //continue;
            } else if (instr.getInstruction().getInputs().containsKey(transferOutDroplet) && instr.getInstruction().getInputs().get(transferOutDroplet) instanceof Instance &&
                    ((Instance) instr.getInstruction().getInputs().get(transferOutDroplet)).getIsStationary()) {
                continue;
            } else if (instr.getInstruction() instanceof Output) {
                continue;
            }
            MFSimSSATransferOut transOut = new MFSimSSATransferOut(uniqueIdGen.getNextID(), transferOutDroplet, transferOutDroplet);
            if (this.transOut.get(transOut.getID()) == null) {
                this.transOut.put(transOut.getID(), new ArrayList<>());
            }
            this.transOut.get(transOut.getID()).add(transOut);
        }

        for (InstructionEdge edge : bb.getEdges()) {
            if (node.containsKey(edge.getDestination())) {//I am a child of
                Integer destination = node.get(edge.getDestination()).getID();
                if (node.containsKey(edge.getSource())) { //another node
                    InstructionNode source = getInstructionNodeByID(bb, edge.getSource());
                    //check if destination uses node's outputs
                    InstructionNode dest = getInstructionNodeByID(bb, edge.getDestination());
                    if (source.getOutputSymbols().size() > 0) {
                        for (String output : source.getOutputSymbols()) {
                            if (dest.getInputSymbols().contains(output)) {
                                MFSimSSANode node = this.node.get(source.getId());
                                node.addSuccessor(destination);
                            }
                        }
                    } else {
                        for (String input : source.getInputSymbols()) {
                            if (dest.getInputSymbols().contains(input)) {
                                MFSimSSANode node = this.node.get(source.getId());
                                node.addSuccessor(destination);
                            }
                        }
                    }
                    //if (node.getID() < destination)
                    //    node.addSuccessor(destination);
                } else if (transIn.containsKey(edge.getSource())) {
                    MFSimSSATransferIn node = transIn.get(edge.getSource()).get(destination);
                    if (node.getID() < destination)
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

                        //find first node the transferred in droplet is used in

                        if (instruction.getUse().contains(in.getTransferedSymbol()))
                            in.addSuccessor(node.get(instruction.getId()).getID());
                        else if (node.containsKey(in.getID()))
                            in.addSuccessor(node.get(in.getID()).getID());
                        break;
                    }
                    //in.addSuccessor(nodes.get(bb.getStatements().get(0).getId()).getID());
                } else {
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
                    for (Integer instrIndex = bb.getInstructions().size() - 1; ; --instrIndex) {
                        InstructionNode instruction = bb.getInstructions().get(instrIndex);
                        if (instruction.getId() > 0) {
                            node.get(instruction.getId()).addSuccessor(out.getID());
                            break;
                        }
                    }
                } else {
                    // do nothing, transIn should take care of the edge between the two
                }
            }
        }

        for (InstructionNode drain : needToDrain) {
            if (drain.getInstruction() instanceof Output)
                continue;
            if (!(node.get(drain.getId()).getSuccessorIDs().size() > 0)) {
                MFSimSSAOutput out = new MFSimSSAOutput(uniqueIdGen.getNextID(), new Output("Drain"));
                node.put(out.getID(), out);
                node.get(drain.getId()).addSuccessor(out.getID());
            }
        }


    }

    private InstructionNode getInstructionNodeByID(BasicBlock bb, Integer id) {
        List<InstructionNode> instructions = bb.getInstructions();
        for (Integer j = 0; j < instructions.size(); ++j) {
            InstructionNode node = instructions.get(j);
            if (node.getId() == id)
                return node;
        }
        return null;
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

    public String toString() {
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