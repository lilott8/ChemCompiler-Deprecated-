package CompilerDataStructures.BasicBlock;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import CompilerDataStructures.InstructionEdge;
import CompilerDataStructures.InstructionNode;
import CompilerDataStructures.StaticSingleAssignment.PHIInstruction;
import CompilerDataStructures.StaticSingleAssignment.StaticSingleAssignment;
import CompilerDataStructures.StaticSingleInformation.SigmaInstruction;
import CompilerDataStructures.StaticSingleInformation.StaticSingleInformation;
import executable.instructions.Instruction;
import executable.instructions.Output;

import java.util.*;

/**
 * Created by Tyson on 4/13/17.
 * Extends a BasicBlock with data dependence edges between instructions
 */
public class DependencySlicedBasicBlock extends BasicBlock{


    public DependencySlicedBasicBlock(BasicBlock bb, StaticSingleAssignment CFG) {
        //copy bb object
        super(bb);

        //don't care about entry/exit block dependencies
        if (CFG.GetEntry() == bb) {
            CFG.SetEntry(this);
            return;
        } else if (CFG.GetExit() == bb) {
            CFG.SetExit(this);
            return;
        }

        //process updates for data dependency edges
        ArrayList<InstructionEdge> instructionEdges = new ArrayList<InstructionEdge>();
        ArrayList<InstructionNode> instructions = new ArrayList<InstructionNode>();
        for (Integer index = 0; index < bb.getInstructions().size(); ++index) {
            InstructionNode instruction = bb.getInstructions().get(index);
            if (instruction instanceof PHIInstruction || instruction instanceof SigmaInstruction)
                continue;
            if (instruction.ID() != -1)
                instructions.add(instruction);
            ProcessInstructionOutput(instruction, instructionEdges, bb, index, CFG);
            ProcessInstructionInput(instruction, instructionEdges, bb, index, CFG);
        }



        // if A->B, A->C and B->C then A->C is redundant
        RemoveRedundancies(instructionEdges, bb, CFG);
        //ProcessTransfers(CFG);

        this.getEdges().clear();
        this.getEdges().addAll(instructionEdges);

        Integer index = 0;
        if (instructions.size() > 0) {
            index = instructions.size()-1;
            for (String exitKey : instructions.get(index).getOutSet()) {
                CFG.getBasicBlock(bb.ID()).getBasicBlockExitTable().put(exitKey, new HashSet<Integer>(instructions.get(index).ID()));
            }
        }



    }

    public static void GetInOutSets(StaticSingleAssignment CFG) {
        HashMap<BasicBlock, InstructionNode> firstInstructions = new LinkedHashMap<BasicBlock, InstructionNode>();
        HashMap<BasicBlock, InstructionNode> lastInstructions = new LinkedHashMap<BasicBlock, InstructionNode>();
        ArrayList<InstructionNode> instructions = new ArrayList<InstructionNode>();
        Integer last = 0;
        for (BasicBlock bb : CFG.getBasicBlocks().values()) {
            instructions.addAll(bb.getInstructions());
            last = bb.ID();
        }

        for (BasicBlock bb : CFG.getBasicBlocks().values()) {
            firstInstructions.put(bb, bb.getInstructions().get(0));
            for (InstructionNode i : bb.getInstructions()) {
                if (!(i instanceof SigmaInstruction) && !(i instanceof PHIInstruction)) {
                    firstInstructions.put(bb, i);
                    break;
                }
            }
            lastInstructions.put(bb, bb.getInstructions().get(bb.getInstructions().size()-1));
            for (Integer index = bb.getInstructions().size()-1; index >-1; index--) {
                InstructionNode i = bb.getInstructions().get(index);
                if (!(i instanceof SigmaInstruction) && !(i instanceof PHIInstruction)) {
                    lastInstructions.put(bb, i);
                    break;
                }
            }
//            if (firstInstructions.get(bb) == null) {
//                firstInstructions.put(bb, bb.getInstructions().get(0));
//            }
//            if (lastInstructions.get(bb) == null) {
//                lastInstructions.put(bb, bb.getInstructions().get(bb.getInstructions().size()-1));
//            }
        }
        firstInstructions.remove(CFG.GetEntry());
        firstInstructions.remove(CFG.GetExit());
        lastInstructions.remove(CFG.GetExit());
        lastInstructions.remove(CFG.GetEntry());

        //ignore instructions from entry node
        for (Integer i = 0; i < CFG.getBasicBlocks().get(0).getInstructions().size(); i++) {
            instructions.remove(0);
        }
        //ignore instructions from exit node
        for (Integer i = 0; i < CFG.getBasicBlock(last).getInstructions().size(); i++) {
            instructions.remove(instructions.size()-1);
        }

        //ignore phi and sigma instructions
        for (Integer i = instructions.size()-1; i > 0; i--) {
            InstructionNode instr = instructions.get(i);
            if (instr instanceof PHIInstruction || instr instanceof SigmaInstruction) {
                instructions.remove(instr);
            }
        }


        for (Integer index = 0; index < instructions.size(); ++index) {
            InstructionNode instr = instructions.get(index);
            //if phi or sigma, remove from
            if (instr instanceof PHIInstruction || instr instanceof SigmaInstruction) {
                //continue;
            }
            try {
                ArrayList<LinkedHashSet<String>> def_use = new ArrayList<LinkedHashSet<String>>();
                LinkedHashSet<String> _defs = new LinkedHashSet<String>();
                LinkedHashSet<String> _uses = new LinkedHashSet<String>();
                if (instr.Instruction() != null) {
                    for (String def : instr.Instruction().getOutputs().keySet()) {
                        _defs.add(def);
                    }
                    for (String use : instr.Instruction().getInputs().keySet()) {
                        _uses.add(use);
                    }
                }
                else {
                    if (instr instanceof PHIInstruction) {
                        _defs.add(((PHIInstruction) instr).getOriginalName());
                        _uses.add(((PHIInstruction) instr).getOriginalName());
                    }
                    else if (instr instanceof SigmaInstruction) {
                        _defs.add(instr.getInputSymbols().get(0));
                        _defs.add(instr.getInputSymbols().get(0));
                    }
                    else {
                        System.out.print("error");
                    }
                }

                def_use.add(_defs);
                def_use.add(_uses);
                instr.set_def(def_use.remove(0));
                instr.set_use(def_use.remove(0));
                for (String var : instr.get_use()) {
                    if (!CFG.GetEntry().getDefinitions().contains(var))
                        instr.getInSet().add(var);
                }


                if (index != 0) {
                    instr.get_pred().add(instructions.get(index - 1));
                    instructions.get(index - 1).get_succ().add(instr);
                }
                if (index <= instructions.size() - 2) {
                    instr.get_succ().add(instructions.get(index + 1));
                    instructions.get(index + 1).get_pred().add(instr);
                }

            } catch (Exception e) {
                e.printStackTrace();
            }
        }

        boolean changed = true;
        while (changed) {
            changed = false;
            for (Integer index = instructions.size() - 1; index > -1; index--) {
                InstructionNode instr = instructions.get(index);
                if (instr instanceof PHIInstruction || instr instanceof SigmaInstruction) {
                    continue;
                }

                //OUT[n] = U {s in succ(n)} IN[s]
                for (InstructionNode succ : instr.get_succ()) {
                    for (String var : succ.getInSet()) {
                        if (!(instr.getOutSet().contains(var))) {
                            instr.getOutSet().add(var);
                            changed = true;
                        }
                    }
                }

                //IN[n] = USE[n] U (OUT[n] - DEF[n])
                for (String var : instr.get_use()) {
                    if (!(instr.getInSet().contains(var))) {
                        if (!CFG.GetEntry().getDefinitions().contains(var)) {
                            instr.getInSet().add(var);
                            changed = true;
                        }
                    }
                }
                for (String var : instr.getOutSet()) {
                    if (!(instr.get_def().contains(var))) {
                        if (!(instr.getInSet().contains(var))) {
                            if (!CFG.GetEntry().getDefinitions().contains(var)) {
                                instr.getInSet().add(var);
                                changed = true;
                            }
                        }
                    }
                }

            }
        }
        instructions.get(0).getInSet().clear();

        //Get Dispense symbols
        for (InstructionNode instruction : instructions) {
            for (String instructionInput : instruction.Instruction().getInputs().keySet()) {
                if (CFG.GetEntry().getDefinitions().contains(instructionInput)) {
                    instruction.addImplicitDispense(instructionInput);
                }
            }
        }


        for (BasicBlock bb: CFG.getBasicBlocks().values()) {
            InstructionNode firstInstruction = firstInstructions.get(bb);
            InstructionNode lastInstruction = lastInstructions.get(bb);

            if (bb == CFG.GetEntry() || bb == CFG.GetExit()) {
                continue;
            }
            //get transfer ins
            for (String in : firstInstruction.getInSet()) {
                if (bb != null && bb != CFG.GetEntry() && bb != CFG.GetExit()) {
                    if (!bb.getBasicBlockEntryTable().containsKey(in)) {
                        bb.getBasicBlockEntryTable().put(in, new HashSet<Integer>());
                    }
                    bb.getBasicBlockEntryTable().get(in).add(firstInstruction.ID());
                }
            }

            if (bb.getBasicBlockEntryTable().isEmpty()) {
                if (firstInstruction.isLeader()) {
                    //do nothing
                } else {
                    //check Exit table for bb's leading to this bb, transfer in and out those variables
                    for (BasicBlockEdge edge : CFG.getBasicBlockEdges()) {
                        if (edge.getDestination() == bb.ID()) {
                            for (String var : CFG.getBasicBlock(edge.getSource()).getBasicBlockExitTable().keySet()) {
                                if (!bb.getBasicBlockEntryTable().containsKey(var)) {
                                    bb.getBasicBlockEntryTable().put(var, new HashSet<Integer>());
                                }
                                bb.getBasicBlockEntryTable().get(var).add(firstInstruction.ID());
                                if (!bb.getBasicBlockExitTable().containsKey(var)) {
                                    bb.getBasicBlockExitTable().put(var, new HashSet<Integer>());
                                }
                                bb.getBasicBlockExitTable().get(var).add(firstInstruction.ID());
                            }
                        }
                    }
                    //transfer in and out all phi and sigma inputs
 /*                   for (InstructionNode instr : bb.getInstructions()) {
                        for (String in : instr.getInputSymbols()) {
                            if (CFG.GetEntry().getDefinitions().contains(in)) {
                                continue;
                            }
                            else {
                                if (!bb.getBasicBlockEntryTable().containsKey(in)) {
                                    bb.getBasicBlockEntryTable().put(in, new HashSet<Integer>());
                                }
                                bb.getBasicBlockEntryTable().get(in).add(firstInstruction.ID());
                                if (!bb.getBasicBlockExitTable().containsKey(in)) {
                                    bb.getBasicBlockExitTable().put(in, new HashSet<Integer>());
                                }
                                bb.getBasicBlockExitTable().get(in).add(firstInstruction.ID());
                                break;
                            }
                        }
                        if (!bb.getBasicBlockEntryTable().isEmpty()) {
                            break;
                        }
                    }
*/
                }
            }

            //get transfer outs
            for (String out : lastInstruction.getOutSet()) {
                if (bb != null && bb != CFG.GetEntry() && bb != CFG.GetExit()) {
                    if (!bb.getBasicBlockExitTable().containsKey(out)) {
                        bb.getBasicBlockExitTable().put(out, new HashSet<Integer>());
                    }
                    bb.getBasicBlockExitTable().get(out).add(lastInstruction.ID());
                }
            }

//            if (bb.getBasicBlockExitTable().isEmpty()) {
//                if (lastInstruction.Instruction() instanceof Output) {
//                    //do nothing
//                } else {
//                    //transfer in and out all phi and sigma inputs
//                    for (InstructionNode instr : bb.getInstructions()) {
//                        for (String out : instr.getOutputSymbols()) {
//                            if (CFG.GetEntry().getDefinitions().contains(out)) {
//                                continue;
//                            }
//                            else {
//                                if (!bb.getBasicBlockExitTable().containsKey(out)) {
//                                    bb.getBasicBlockExitTable().put(out, new HashSet<Integer>());
//                                }
//                                bb.getBasicBlockExitTable().get(out).add(lastInstruction.ID());
//                            }
//                        }
//                    }
//                }
//            }



        }

    }

    private void ProcessInstructionInput(InstructionNode instruction, ArrayList<InstructionEdge> update, BasicBlock bb, Integer index, StaticSingleAssignment CFG) {

        // loop through all inputs (reads)
        for (String inputKey : instruction.getInputSymbols()) {


            for (Integer successorIndex=index+1; successorIndex < bb.getInstructions().size(); ++successorIndex) {
                InstructionNode successor = bb.getInstructions().get(successorIndex);
                //check if input is used by successor
                if (successor.getInputSymbols().contains(inputKey) && successor.ID() != -1) {
                    // input of successor matches input of predecessor, RAR dependency
                    update.add(new InstructionEdge(instruction.ID(), successor.ID()));
                }
            }
        }
    }

    private void ProcessInstructionOutput(InstructionNode instruction, ArrayList<InstructionEdge> update, BasicBlock bb, Integer index, StaticSingleAssignment CFG) {
        // loop through all outputs (writes)
        Set<Integer> exitTable = new HashSet<Integer>();

        for (String outputKey : instruction.getOutputSymbols()) {
            exitTable.add(instruction.ID());

            // currently putting each instructions outputs into the exit table for the basic block,
            // not necesarily needed, only outputs from last instruction needed
            //bb.getBasicBlockExitTable().put(outputKey, exitTable);

            for (Integer successorIndex=index+1; successorIndex < bb.getInstructions().size(); ++successorIndex) {
                InstructionNode successor = bb.getInstructions().get(successorIndex);
                //check if output is used by successor (read)
                if (successor.getInputSymbols().contains(outputKey) && successor.ID() != -1) {
                    // input of successor matches output of predecessor, RAW dependency
                    update.add(new InstructionEdge(instruction.ID(), successor.ID()));
                }
            }
        }
    }


    //removes redundant transitive edges (A->B, A->{C, D, ...}, B->{C, D, ...} :: A->{C, D...} is redundant)
    private void RemoveRedundancies(ArrayList<InstructionEdge> update, BasicBlock bb, StaticSingleAssignment CFG) {
        LinkedHashMap<Integer, LinkedHashSet<Integer>> sourceDestsMap = new LinkedHashMap<Integer, LinkedHashSet<Integer>>();

        //populate hashmap
        for (InstructionEdge edge : update) {
            if (!sourceDestsMap.containsKey(edge.getSource())) {
                sourceDestsMap.put(edge.getSource(), new LinkedHashSet<Integer>());
            }
            sourceDestsMap.get(edge.getSource()).add(edge.getDestination());
        }


        HashMap<Integer, LinkedHashSet<Integer>> remove = new HashMap<Integer, LinkedHashSet<Integer>>();
        //A->
        for (Integer source : sourceDestsMap.keySet()) {
            //{B, ...}
            LinkedHashSet<Integer> dests = sourceDestsMap.get(source);
            //B->
            for (Integer dest : dests) {
                //{C, ...}
                LinkedHashSet<Integer> dest_dests = sourceDestsMap.get(dest);
                if (dest_dests != null) {
                    for (Integer dest_dest : dest_dests) {
                        //check for redundancy
                        if (dests.contains(dest_dest)) {
                            if (!remove.containsKey(source)) {
                                remove.put(source, new LinkedHashSet<Integer>());
                            }
                            remove.get(source).add(dest_dest);
                        }
                    }
                }
            }
        }

        //remove redundancies from sourceDests map
        for (Integer source : remove.keySet()) {
            sourceDestsMap.get(source).removeAll(remove.get(source));
        }

        //update instructionEdge list
        for (Integer i = update.size()-1; i > -1; i--) {
            Integer source = update.get(i).getSource();
            if (!sourceDestsMap.get(source).contains(update.get(i).getDestination())) {
                update.remove(i.intValue());
            }
        }

        //remove repeat edges
        for (Integer i = 0; i < update.size(); i++) {
            for (Integer j = i+1; j < update.size(); j++) {
                if (update.get(i).equals(update.get(j))) {
                    update.remove(j.intValue());
                    j--;
                }
            }
        }

    }

    private ArrayList<Integer> getDestinations(Integer source, ArrayList<InstructionEdge> edges) {
        ArrayList<Integer> destinations = new ArrayList<Integer>();
        for (Integer edgeIndex = 0; edgeIndex < edges.size(); ++edgeIndex) {
            InstructionEdge edge = edges.get(edgeIndex);
            if (!(edge.getSource().equals(source))) {
                continue;
            }
            destinations.add(edge.getDestination());
            //get all destinations of source
            for (Integer destIndex = edgeIndex+1; destIndex < edges.size(); ++destIndex) {
                InstructionEdge destNode = edges.get(destIndex);
                if (destNode.getSource().equals(source)) {
                    ++edgeIndex;
                    destinations.add(destNode.getDestination());
                }
            }
        }
        return destinations;
    }
}