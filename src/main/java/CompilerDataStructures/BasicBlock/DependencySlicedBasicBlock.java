package CompilerDataStructures.BasicBlock;
import CompilerDataStructures.InstructionEdge;
import CompilerDataStructures.InstructionNode;
import CompilerDataStructures.StaticSingleAssignment.SemiPrunedStaticSingleAssignment.SemiPrunedStaticSingleAssignment;

import java.util.*;

/**
 * Created by Tyson on 4/13/17.
 * Extends a BasicBlock with data dependence edges between instructions
 */
public class DependencySlicedBasicBlock extends BasicBlock{


    public DependencySlicedBasicBlock(BasicBlock bb, SemiPrunedStaticSingleAssignment SPSSA) {
        //copy bb object
        super(bb);

        //process updates for data dependency edges
        ArrayList<InstructionEdge> instructionEdges = new ArrayList<InstructionEdge>();
        for (Integer index = 0; index < bb.getInstructions().size(); ++index) {
            InstructionNode instruction = bb.getInstructions().get(index);
            ProcessInstructionInput(instruction, instructionEdges, bb, index, SPSSA);
            ProcessInstructionOutput(instruction, instructionEdges, bb, index);
        }

        // if A->B, A->C and B->C then A->C is redundant
        RemoveRedundancies(instructionEdges, bb);
    }

    private void ProcessInstructionInput(InstructionNode instruction, ArrayList<InstructionEdge> update, BasicBlock bb, Integer index, SemiPrunedStaticSingleAssignment SPSSA) {

        // loop through all inputs (reads)
        for (String inputKey : instruction.getInputSymbols()) {


            //get dispense instructions
            ArrayList<Integer> predecessors = new ArrayList<Integer>(SPSSA.getPredecessors(bb.ID()));
            for (Integer i = predecessors.size(); i > 0; --i) {
                for (InstructionNode instr : SPSSA.getBasicBlock(predecessors.get(i-1)).getInstructions()) {
                    if (instr.getOutputSymbols().contains(inputKey)) {
                        instruction.addImplicitDispense(inputKey);
                    }
                }
            }

            for (Integer successorIndex=index+1; successorIndex < bb.getInstructions().size(); ++successorIndex) {
                InstructionNode successor = bb.getInstructions().get(successorIndex);
                //check if input is used by successor
                if (successor.getInputSymbols().contains(inputKey)) {
                    // input of successor matches input of predecessor, RAR dependency
                    update.add(new InstructionEdge(instruction.ID(), successor.ID()));
                }
            }
        }
    }

    private void ProcessInstructionOutput(InstructionNode instruction, ArrayList<InstructionEdge> update, BasicBlock bb, Integer index) {
        // loop through all outputs (writes)
        Set<Integer> exitTable = new HashSet<Integer>();
        for (String outputKey : instruction.getOutputSymbols()) {
            exitTable.add(instruction.ID());
            bb.getBasicBlockExitTable().put(outputKey, exitTable);
            for (Integer successorIndex=index+1; successorIndex < bb.getInstructions().size(); ++successorIndex) {
                InstructionNode successor = bb.getInstructions().get(successorIndex);
                //check if output is used by successor (read)
                if (successor.getInputSymbols().contains(outputKey)) {
                    // input of successor matches output of predecessor, RAW dependency
                    update.add(new InstructionEdge(instruction.ID(), successor.ID()));
                }
            }
        }
    }


    //removes redundant transitive edges (A->B, A->{C, D, ...}, B->{C, D, ...} :: A->{C, D...} is redundant)
    private void RemoveRedundancies(ArrayList<InstructionEdge> update, BasicBlock bb) {
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