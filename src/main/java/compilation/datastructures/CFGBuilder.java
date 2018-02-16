package compilation.datastructures;

import java.util.ArrayList;
import java.util.List;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.cfg.CFG;
import executable.Executable;
import executable.Experiment;
import executable.conditionals.Branch;
import executable.conditionals.Loop;
import executable.instructions.Instruction;

/**
 * Created by chriscurtis on 10/13/16.
 */
public class CFGBuilder {

    private static BasicBlock insertExitNode(List<BasicBlock> exitNodes, CFG cfg){
        BasicBlock EXIT = cfg.newBasicBlock();
        for(BasicBlock bb : exitNodes)
            cfg.addEdge(bb, EXIT);
        return EXIT;
    }
    /*
        The insertion of ENTRY and EXIT nodes follow the data structure for the algorithms that are presented in Cytron et. al.
        "An efficient Method of Computing Static Single Assignment Form".
     */
    private static CFG buildControlFlowGraph(Integer id, List<Instruction> instructions) throws Exception{
        CFG controlFlowGraph = new CFG();

        BasicBlock entryNode = controlFlowGraph.newBasicBlock();
        controlFlowGraph.setEntry(entryNode);

        BasicBlock startOfInstructions = controlFlowGraph.newBasicBlock();
        controlFlowGraph.addEdge(entryNode, startOfInstructions);

        List<BasicBlock> danglingExitNodes = processNestedInstructions(controlFlowGraph, startOfInstructions, instructions);

        BasicBlock exitNode = insertExitNode(danglingExitNodes, controlFlowGraph);
        controlFlowGraph.addEdge(entryNode, exitNode);
        controlFlowGraph.setExit(exitNode);

        return controlFlowGraph;
    }

    public static CFG buildControlFlowGraph(Experiment experiment)throws Exception{

        List<Instruction> instructions = new ArrayList<>();
        for(Executable e :experiment.getInstructions()){
            if (e instanceof Instruction) {
                instructions.add((Instruction) e);
            }
        }
        CFG controlFlowGraph = buildControlFlowGraph(0, instructions);

        //Add definition of Global Input at Entry Node.
        for(String globalInput : experiment.getInputs().keySet()) {
            controlFlowGraph.getEntry().getDefinitions().add(globalInput);
        }
        return controlFlowGraph;
    }
    /*
     * Method; Process Branch
     *
     * Input: CFG , SSI.SSA.basicblock, Branch
     *      The basic block(BB) passed in represents the BB that was being processed when the Branch is triggered.
     *
     */
    private static List<BasicBlock> processBranch(CFG controlFlowGraph, BasicBlock bb, Branch branch) throws Exception{
        List<BasicBlock> leaves = new ArrayList<BasicBlock>();
        if (branch != null) {
            BasicBlock trueBranchEntryBasicBlock = controlFlowGraph.newBasicBlock();
            controlFlowGraph.addEdge(bb,trueBranchEntryBasicBlock, branch.getCondition(), branch.getName());

            leaves.addAll(processNestedInstructions(controlFlowGraph, trueBranchEntryBasicBlock, branch.getTrueBranch()));

            for(int instructionsIndex = 0; instructionsIndex < branch.getElseIfBranch().size(); ++instructionsIndex){
                Instruction elseIfBranch = branch.getElseIfBranch().get(instructionsIndex);
                BasicBlock elseIfBranchEntryBasicBlock = controlFlowGraph.newBasicBlock();
                controlFlowGraph.addEdge(bb,elseIfBranchEntryBasicBlock);

                List<BasicBlock> dangledLeaves = processBranch(controlFlowGraph, elseIfBranchEntryBasicBlock, (Branch)elseIfBranch);

                if( !branch.getElseBranch().isEmpty() || instructionsIndex < branch.getElseIfBranch().size()-1) {
                    for (int i = 0; i < dangledLeaves.size()-1; ++i) {
                        leaves.add(dangledLeaves.get(i));
                    }
                }
                else {
                    leaves.addAll(dangledLeaves);
                }

                bb = elseIfBranchEntryBasicBlock;
            }
            if( branch.getElseIfBranch().size() > 0) {
                BasicBlock elseBranchBasicBlock = controlFlowGraph.newBasicBlock();
                controlFlowGraph.addEdge(bb, elseBranchBasicBlock);

                leaves.addAll(processNestedInstructions(controlFlowGraph, elseBranchBasicBlock, branch.getElseBranch()));
            }
            if(branch.getElseBranch().isEmpty())
                leaves.add(bb);
        }
        return leaves;
    }
    /*
      * Method; Process Branch
      *
      * Input: CFG , SSI.SSA.basicblock, Control
      *      The basic block(BB) passed in represents the BB that was being processed when the Branch is triggered.
      *
      */
    private static BasicBlock processLoop(CFG controlFlowGraph, BasicBlock bb, Loop loop) throws Exception{

        if (loop != null) {
            BasicBlock whileConditionEntry = controlFlowGraph.newBasicBlock();
            BasicBlock whileEntry = controlFlowGraph.newBasicBlock();

            controlFlowGraph.addEdge(bb,whileConditionEntry);
            controlFlowGraph.addEdge(whileConditionEntry,whileEntry,loop.getCondition(), loop.getName());

            List<BasicBlock> loopLeaves = processNestedInstructions(controlFlowGraph,whileEntry,loop.getTrueBranch());

            /*
             *  **NOTE** if While MUST EXIT from single location:
             *  if loopLeaves > 1
             *      create Control exit
             *      add leaves to exit
             *      add exit to whileConditionEntry
             *  else
             *      add loopLeaves[0] to whileConditionEntry
             */

            for(BasicBlock leaf: loopLeaves) {
                controlFlowGraph.addEdge(leaf,whileConditionEntry);
            }
            return whileConditionEntry;
        }
        throw new Exception("Processing Null Exception");
    }

    private static List<BasicBlock> processNestedInstructions(CFG controlFlowGraph, BasicBlock bb, List<Instruction> instructionList) throws Exception {

        for (int instructionIndex = 0; instructionIndex < instructionList.size(); ++instructionIndex) {
            Instruction instruction = instructionList.get(instructionIndex);
            bb.addVariableDefinition(instruction);

            if (instruction instanceof Branch) {
                List<BasicBlock> branchLeaves = processBranch(controlFlowGraph, bb, (Branch) instruction);

                if (instructionIndex < instructionList.size() - 1) {
                    BasicBlock postBranchBasicBlock = controlFlowGraph.newBasicBlock();

                    for (BasicBlock branchLeaf : branchLeaves) {
                        controlFlowGraph.addEdge(branchLeaf, postBranchBasicBlock);
                    }
                    bb = postBranchBasicBlock;
                } else if (instructionIndex == instructionList.size() - 1) {//if last instruction pass back this group of edges
                    return branchLeaves;
                }

            } else if (instruction instanceof Loop) {
                BasicBlock loopEntry = processLoop(controlFlowGraph, bb, (Loop) instruction);

                if (instructionIndex < instructionList.size() - 1) {
                    BasicBlock postLoopBasicBlock = controlFlowGraph.newBasicBlock();

                    controlFlowGraph.addEdge(loopEntry, postLoopBasicBlock);

                    bb = postLoopBasicBlock;
                } else if (instructionIndex == instructionList.size() - 1) {//if last instruction pass back this Control
                    List<BasicBlock> loopTermination = new ArrayList<BasicBlock>();
                    loopTermination.add(loopEntry);
                    return loopTermination;
                }
            } else {
                if (instructionIndex == 0) {
                    controlFlowGraph.insertInstructionNode(bb, instruction, true);
                }
                else {
                    controlFlowGraph.insertInstructionNode(bb, instruction, false);
                }

                if (instructionIndex == instructionList.size() - 1) {
                    List<BasicBlock> listTermination = new ArrayList<>();
                    listTermination.add(bb);
                    return listTermination;
                }
            }
        }

        List<BasicBlock> ret = new ArrayList<>();
        ret.add(bb);
        return ret;
    }

}
