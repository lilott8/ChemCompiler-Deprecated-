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

/**
 * Created by Tyson on 4/13/17.
 * Extends a BasicBlock with data dependence edges between instructions
 */
public class DependencySlicedBasicBlock extends BasicBlock{


    public DependencySlicedBasicBlock(BasicBlock bb, StaticSingleAssignment CFG) {
        //copy bb object
        super(bb);

        if (CFG.GetEntry() == bb || CFG.GetExit() == bb) {
            return; //don't care about entry/exit block
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

        GetInOutSets(CFG);

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

    private void GetInOutSets(StaticSingleAssignment CFG) {
        ArrayList<InstructionNode> instructions = new ArrayList<InstructionNode>();
        Integer last = 0;
        for (BasicBlock bb : CFG.getBasicBlocks().values()) {
            instructions.addAll(bb.getInstructions());
            last = bb.ID();
        }

        //ignore instructions from entry node
        for (Integer i = 0; i < CFG.getBasicBlocks().get(0).getInstructions().size(); i++) {
            instructions.remove(0);
        }
        //ignore instructions from exit node
        for (Integer i = 0; i < CFG.getBasicBlock(last).getInstructions().size(); i++) {
            instructions.remove(instructions.size()-1);
        }


        for (Integer index = 0; index < instructions.size(); ++index) {
            InstructionNode instr = instructions.get(index);
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
                        instr.getInSet().add(var);
                        changed = true;
                    }
                }
                for (String var : instr.getOutSet()) {
                    if (!(instr.get_def().contains(var))) {
                        if (!(instr.getInSet().contains(var))) {
                            instr.getInSet().add(var);
                            changed = true;
                        }
                    }
                }

            }
        }
        instructions.get(0).getInSet().clear();

        for (BasicBlock bb: CFG.getBasicBlocks().values()) {
            InstructionNode firstInstruction = bb.getInstructions().get(0);
            InstructionNode lastInstruction = bb.getInstructions().get(bb.getInstructions().size()-1);
            for (InstructionNode instruction : instructions) {
                for (String use : instruction.get_use()) {
                    if (!instruction.getInSet().contains(use)) {
                        instruction.addImplicitDispense(use);
                    }
                }
            }

            for (String in : firstInstruction.getInSet()) {
                if (bb != null && bb != CFG.GetEntry() && bb != CFG.GetExit()) {
                    if (!bb.getBasicBlockEntryTable().containsKey(in)) {
                        bb.getBasicBlockEntryTable().put(in, new HashSet<Integer>());
                    }
                    bb.getBasicBlockEntryTable().get(in).add(firstInstruction.ID());
                }
            }

            for (String out : lastInstruction.getOutSet()) {
                if (bb != null && bb != CFG.GetEntry() && bb != CFG.GetExit()) {
                    if (!bb.getBasicBlockExitTable().containsKey(out)) {
                        bb.getBasicBlockExitTable().put(out, new HashSet<Integer>());
                    }
                    bb.getBasicBlockExitTable().get(out).add(lastInstruction.ID());
                }
            }
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
        ArrayList<InstructionEdge> instructionEdges = new ArrayList<InstructionEdge>();
        ArrayList<Integer> destinations = new ArrayList<Integer>();
        for (Integer edgeIndex = 0; edgeIndex < update.size(); ++edgeIndex) {
            destinations.clear();
            InstructionEdge edge = update.get(edgeIndex);
            Integer source = edge.getSource();
            destinations.add(edgeIndex);
            //get all destinations of source
            for (Integer destIndex = edgeIndex+1; destIndex < update.size(); ++destIndex) {
                InstructionEdge destNode = update.get(destIndex);
                if (destNode.getSource().equals(source)) {
                    ++edgeIndex;
                    destinations.add(destIndex);
                }
            }
            for (Integer i = 0; i < destinations.size(); ++i) {  //A->B
                for (Integer j = i + 1; j < destinations.size(); ++j) { //B->{C, D, ...}
                    //if edge from i->j, remove j from destinations
                    Integer dest1 = update.get(destinations.get(i)).getDestination();

                    //get destinations of dest1
                    ArrayList<Integer> redundancies = getDestinations(dest1, update); //A->{...}
                    Integer dest2 = update.get(destinations.get(j)).getDestination();
                    if (redundancies.contains(dest2) || dest1.equals(dest2)) {
                        destinations.remove(j.intValue());
                    }
                }
            }
            for (Integer destination : destinations) {
                instructionEdges.add(update.get(destination));
            }
        }
        for (InstructionEdge edge : instructionEdges) {
            bb.addEdge(edge.getSource(), edge.getDestination());
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