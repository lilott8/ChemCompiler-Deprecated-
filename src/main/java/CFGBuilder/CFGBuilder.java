package CFGBuilder;

import DominatorTree.DominatorTree;
import SymbolTable.NestedSymbolTable;
import executable.Executable;
import executable.conditionals.Branch;
import executable.conditionals.Loop;
import executable.instructions.Instruction;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 10/13/16.
 */
public class CFGBuilder {

    private static CFG BuildControlFlowGraph(Integer id, List<Instruction> instructions, NestedSymbolTable table) throws Exception{
        CFG controlFlowGraph = new CFG(id, table);

        ProcessNestedInstructions(controlFlowGraph, controlFlowGraph.newBasicBlock(), instructions);

        controlFlowGraph.addDominatorTree(new DominatorTree(controlFlowGraph));
        controlFlowGraph.renameVariables();
        return controlFlowGraph;
    }

    /*public static CFG BuildControlFlowGraph(List<Instruction> instructions)throws Exception{
        return BuildControlFlowGraph(0,instructions);
    }*/
    public static CFG BuildControlFlowGraph(List<Executable> executables,NestedSymbolTable table)throws Exception{

        List<Instruction> instructions = new ArrayList<Instruction>();
        for(Executable e :executables){
            if (e instanceof Instruction)
                instructions.add((Instruction)e);
        }


        return BuildControlFlowGraph(0,instructions,table);
    }


    /*
     * Method; Process Branch
     *
     * Input: CFG , BasicBlock, Branch
     *      The basic block(BB) passed in represents the BB that was being processed when the Branch is triggered.
     *
     */
    private static List<BasicBlock> ProcessBranch( CFG controlFlowGraph, BasicBlock bb, Branch branch) throws Exception{
        List<BasicBlock> leaves = new ArrayList<BasicBlock>();
        if (branch != null) {
//            controlFlowGraph.setSymbolTable(controlFlowGraph.getSymbolTable().nestTable());
            BasicBlock trueBranchEntryBasicBlock = controlFlowGraph.newBasicBlock();
            controlFlowGraph.addEdge(bb,trueBranchEntryBasicBlock, branch.getCondition());

            for(BasicBlock processedBasicBlock: ProcessNestedInstructions(controlFlowGraph, trueBranchEntryBasicBlock, branch.getTrueBranch())) {
                leaves.add(processedBasicBlock);
            }
            for(Instruction elseIfBranch : branch.getElseIfBranch()) {
                BasicBlock elseIfBranchEntryBasicBlock = controlFlowGraph.newBasicBlock();
                controlFlowGraph.addEdge(bb,elseIfBranchEntryBasicBlock);

                for(BasicBlock processedBasicBlock: ProcessBranch(controlFlowGraph, elseIfBranchEntryBasicBlock, (Branch)elseIfBranch)) {
                    leaves.add(processedBasicBlock);
                }

                bb = elseIfBranchEntryBasicBlock;
            }
            if( branch.getElseIfBranch().size() > 0) {
                BasicBlock elseBranchBasicBlock = controlFlowGraph.newBasicBlock();
                controlFlowGraph.addEdge(bb, elseBranchBasicBlock);

                for(BasicBlock processedBasicBlock: ProcessNestedInstructions(controlFlowGraph, elseBranchBasicBlock, branch.getElseBranch())) {
                    leaves.add(processedBasicBlock);
                }
            }
            leaves.add(bb);
        }
        return leaves;
    }
    /*
      * Method; Process Branch
      *
      * Input: CFG , BasicBlock, Loop
      *      The basic block(BB) passed in represents the BB that was being processed when the Branch is triggered.
      *
      */
    private static BasicBlock ProcessLoop(CFG controlFlowGraph, BasicBlock bb, Loop loop) throws Exception{

        if (loop != null) {
            BasicBlock whileConditionEntry = controlFlowGraph.newBasicBlock();
            BasicBlock whileEntry = controlFlowGraph.newBasicBlock();

            controlFlowGraph.addEdge(bb,whileConditionEntry);
            controlFlowGraph.addEdge(whileConditionEntry,whileEntry,loop.getCondition());

            List<BasicBlock> loopLeaves = ProcessNestedInstructions(controlFlowGraph,whileEntry,loop.getTrueBranch());

            /*
             *  **NOTE** if While MUST EXIT from single location:
             *  if loopLeaves > 1
             *      create Loop exit
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

    private static List<BasicBlock> ProcessNestedInstructions(CFG controlFlowGraph, BasicBlock bb, List<Instruction> instructionList) throws Exception {

        for (int instructionIndex = 0; instructionIndex < instructionList.size(); ++instructionIndex) {
            Instruction instruction = instructionList.get(instructionIndex);
            if (instruction instanceof Branch) {
                List<BasicBlock> branchLeaves = ProcessBranch(controlFlowGraph, bb, (Branch) instruction);

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
                BasicBlock loopEntry = ProcessLoop(controlFlowGraph, bb, (Loop) instruction);

                if (instructionIndex < instructionList.size() - 1) {
                    BasicBlock postLoopBasicBlock = controlFlowGraph.newBasicBlock();

                    controlFlowGraph.addEdge(loopEntry, postLoopBasicBlock);

                    bb = postLoopBasicBlock;
                } else if (instructionIndex == instructionList.size() - 1) {//if last instruction pass back this Loop
                    List<BasicBlock> loopTermination = new ArrayList<BasicBlock>();
                    loopTermination.add(loopEntry);
                    return loopTermination;
                }
            } else {
                if (instructionIndex == 0)
                    controlFlowGraph.insertInstructionNode(bb, instruction, true);
                else
                    controlFlowGraph.insertInstructionNode(bb, instruction, false);


                if (instructionIndex == instructionList.size() - 1) {
                    List<BasicBlock> listTermination = new ArrayList<BasicBlock>();
                    listTermination.add(bb);
                    return listTermination;
                }
            }
        }

        List<BasicBlock> ret = new ArrayList<BasicBlock>();
        ret.add(bb);
        return ret;
    }

}
