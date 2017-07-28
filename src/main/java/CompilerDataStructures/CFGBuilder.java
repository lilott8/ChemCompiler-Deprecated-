package CompilerDataStructures;

import java.util.ArrayList;
import java.util.List;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import executable.Executable;
import executable.Experiment;
import executable.conditionals.Branch;
import executable.conditionals.Loop;
import executable.instructions.Instruction;

/**
 * Created by chriscurtis on 10/13/16.
 */
public class CFGBuilder {



    private static BasicBlock InsertExitNode(List<BasicBlock> exitNodes, CFG cfg){
        BasicBlock EXIT = cfg.newBasicBlock();
        for(BasicBlock bb : exitNodes)
            cfg.addEdge(bb, EXIT);
        return EXIT;
    }


    /*
        The insertion of ENTRY and EXIT nodes follow the data structure for the algorithms that are presented in Cytron et. al.
        "An efficient Method of Computing Static Single Assignment Form".
     */
    private static CFG BuildControlFlowGraph(Integer id, List<Instruction> instructions) throws Exception{
        CFG controlFlowGraph = new CFG();

        BasicBlock entryNode = controlFlowGraph.newBasicBlock();
        controlFlowGraph.SetEntry(entryNode);

        BasicBlock startOfInstructions = controlFlowGraph.newBasicBlock();
        controlFlowGraph.addEdge(entryNode, startOfInstructions);

        List <BasicBlock> danglingExitNodes = ProcessNestedInstructions(controlFlowGraph, startOfInstructions, instructions);

        BasicBlock exitNode = InsertExitNode(danglingExitNodes, controlFlowGraph);
        controlFlowGraph.addEdge(entryNode, exitNode);
        controlFlowGraph.SetExit(exitNode);

       // controlFlowGraph.addDominatorTree(new DominatorTree(controlFlowGraph));


      //  for (SSI.SSA.BasicBlock b : danglingLeaves) {
      //      System.out.println(b.getID());
      //  }

        //ReachingDefinitions rdef = new ReachingDefinitions(controlFlowGraph);

        //System.out.println(rdef);
        //System.exit(-1);

        //controlFlowGraph.renameVariables();
        return controlFlowGraph;
    }

    /*public static CFG BuildControlFlowGraph(List<Instruction> instructions)throws Exception{
        return BuildControlFlowGraph(0,instructions);
    }*/
    public static CFG BuildControlFlowGraph(Experiment experiment)throws Exception{

        List<Instruction> instructions = new ArrayList<Instruction>();
        for(Executable e :experiment.getInstructions()){
            if (e instanceof Instruction)
                instructions.add((Instruction)e);
        }
        CFG controlFlowGraph = BuildControlFlowGraph(0,instructions);

        //Add definition of Global Input at Entry Node.
        for(String globalInput : experiment.getInputs().keySet()) {
            controlFlowGraph.GetEntry().getDefinitions().add(globalInput);
        }
        return controlFlowGraph;
    }


    /*
     * Method; Process Branch
     *
     * Input: CFG , SSI.SSA.BasicBlock, Branch
     *      The basic block(BB) passed in represents the BB that was being processed when the Branch is triggered.
     *
     */
    private static List<BasicBlock> ProcessBranch( CFG controlFlowGraph, BasicBlock bb, Branch branch) throws Exception{
        List<BasicBlock> leaves = new ArrayList<BasicBlock>();
        if (branch != null) {
//            controlFlowGraph.setSymbolTable(controlFlowGraph.getSymbolTable().nestTable());
            BasicBlock trueBranchEntryBasicBlock = controlFlowGraph.newBasicBlock();
            controlFlowGraph.addEdge(bb,trueBranchEntryBasicBlock, branch.getCondition(), branch.getName());

            for(BasicBlock processedBasicBlock: ProcessNestedInstructions(controlFlowGraph, trueBranchEntryBasicBlock, branch.getTrueBranch())) {
                leaves.add(processedBasicBlock);
            }


            for(int instructionsIndex = 0; instructionsIndex < branch.getElseIfBranch().size(); ++instructionsIndex){
                Instruction elseIfBranch = branch.getElseIfBranch().get(instructionsIndex);
//            for(Instruction elseIfBranch : branch.getElseIfBranch()) {
                BasicBlock elseIfBranchEntryBasicBlock = controlFlowGraph.newBasicBlock();
                controlFlowGraph.addEdge(bb,elseIfBranchEntryBasicBlock);

                List<BasicBlock> dangledLeaves = ProcessBranch(controlFlowGraph, elseIfBranchEntryBasicBlock, (Branch)elseIfBranch);


                if( !branch.getElseBranch().isEmpty() || instructionsIndex < branch.getElseIfBranch().size()-1) {
                    for (int i = 0; i < dangledLeaves.size()-1; ++i) {
                        leaves.add(dangledLeaves.get(i));
                    }
                }
                else {
                    for (int i = 0; i < dangledLeaves.size(); ++i) {
                        leaves.add(dangledLeaves.get(i));
                    }
                }
//                for(SSI.SSA.BasicBlock processedBasicBlock: dangledLeaves) {

 //               }

                bb = elseIfBranchEntryBasicBlock;
            }
            if( branch.getElseIfBranch().size() > 0) {
                BasicBlock elseBranchBasicBlock = controlFlowGraph.newBasicBlock();
                controlFlowGraph.addEdge(bb, elseBranchBasicBlock);

                for(BasicBlock processedBasicBlock: ProcessNestedInstructions(controlFlowGraph, elseBranchBasicBlock, branch.getElseBranch())) {
                    leaves.add(processedBasicBlock);
                }
            }
            if(branch.getElseBranch().isEmpty())
                leaves.add(bb);
        }
        return leaves;
    }
    /*
      * Method; Process Branch
      *
      * Input: CFG , SSI.SSA.BasicBlock, Loop
      *      The basic block(BB) passed in represents the BB that was being processed when the Branch is triggered.
      *
      */
    private static BasicBlock ProcessLoop(CFG controlFlowGraph, BasicBlock bb, Loop loop) throws Exception{

        if (loop != null) {
            BasicBlock whileConditionEntry = controlFlowGraph.newBasicBlock();
            BasicBlock whileEntry = controlFlowGraph.newBasicBlock();

            controlFlowGraph.addEdge(bb,whileConditionEntry);
            controlFlowGraph.addEdge(whileConditionEntry,whileEntry,loop.getCondition(), loop.getName());

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
            bb.AddVariableDefinition(instruction);

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
