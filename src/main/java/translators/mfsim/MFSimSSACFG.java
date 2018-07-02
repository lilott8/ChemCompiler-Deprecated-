package translators.mfsim;

import com.google.common.base.CharMatcher;
import compilation.datastructures.ssa.PHIInstruction;
import compilation.datastructures.ssi.SigmaInstruction;
import executable.instructions.Instruction;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.BasicBlockEdge;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.node.ConditionalNode;
import compilation.datastructures.node.InstructionNode;
import compilation.datastructures.ssa.StaticSingleAssignment;
import executable.instructions.Output;
import translators.mfsim.operationnode.MFSimSSANode;
import translators.mfsim.operationnode.MFSimSSATransferIn;
import translators.mfsim.operationnode.MFSimSSATransferOut;
import variable.Instance;
import variable.Variable;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSACFG {
    private static final Logger logger = LogManager.getLogger(MFSimSSACFG.class);

    private MFSimSSATranslator.IDGen uniqueIDGen;
    private Map<Integer, MFSimSSADAG> dags;
    private Map<Integer, List<BasicBlockEdge>> conditionalGroups;


    public MFSimSSACFG(CFG controlFlowGraph, MFSimSSATranslator.IDGen uniqueID) {
        uniqueIDGen = uniqueID;
        dags = new LinkedHashMap<>();
        conditionalGroups = new LinkedHashMap<>();

        for (BasicBlock bb : controlFlowGraph.getBasicBlocks().values()) {
            MFSimSSADAG dag = new MFSimSSADAG(bb, uniqueID, ((StaticSingleAssignment) controlFlowGraph).getVariableStack());
            dags.put(bb.getId(), dag);
        }
        ListIterator<BasicBlockEdge> e = controlFlowGraph.getBasicBlockEdges().listIterator();
        while (e.hasNext()) {
            BasicBlockEdge edge = e.next();
            int backup = 0;
            //for each conditional group, source and destination must have executable instructions (not just phi/sigma)

            List<BasicBlockEdge> conditionalGroup;

            if (conditionalGroups.containsKey(edge.getSource())) {
                conditionalGroup = conditionalGroups.get(edge.getSource());
            } else {
                conditionalGroup = new ArrayList<>();
            }

            List<InstructionNode> instructions = controlFlowGraph.getBasicBlock(edge.getSource()).getInstructions();

            if (!(containsLegitInstructions(instructions)) || instructions.get(instructions.size()-1).getInstruction() instanceof Output) {
                boolean stationary = false;
                InstructionNode node = instructions.get(instructions.size()-1);
                if (node.getInstruction() instanceof Output) {
                    for (Variable var : instructions.get(instructions.size() - 1).getInstruction().getInputs().values()) {
                        if (var instanceof Instance && ((Instance) var).getIsStationary()) {
                            stationary = true;
                        }
                    }
                }
                if (!stationary) {
                    e.remove();
                    continue;
                }
            }

            if (!(containsLegitInstructions(controlFlowGraph.getBasicBlock(edge.getDestination()).getInstructions()))) {
                e.remove();
                List<BasicBlockEdge> destEdges = controlFlowGraph.getBasicBlockEdgesBySource(edge.getDestination());


                boolean peaked = false;
                while (destEdges.size() == 1) { // find destination with legitimate statements
                    if (!(containsLegitInstructions(controlFlowGraph.getBasicBlock(destEdges.get(0).getDestination()).getInstructions()))) {
                        destEdges = controlFlowGraph.getBasicBlockEdgesBySource(destEdges.get(0).getDestination());
                        peaked = true;
                    }
                    else
                        break;
                }
                //dest has no executable instructions -- this must be a loop entry or pointing to one
                // get entry and exit edges
                // replace the repeat entry
                Iterator<BasicBlockEdge> d = destEdges.iterator();
                String cond = "";
                int head = 0;
                while (d.hasNext()) {
                    BasicBlockEdge dest = d.next();
                    if (dest.getType().equals("repeat")) {
                        head = dest.getDestination();
                        cond = dest.getCondition();
                        e.add(new BasicBlockEdge(edge.getSource(), dest.getDestination(), "UNCONDITIONAL"));
                        e.previous();
                        d.remove();
                    }
                }
                // dest edges should now only have a single edge, the exit edge --- we need to connect exit edge
                // from the end of the repeat loop for MFSim
                List<BasicBlockEdge> killEdges;
                if (peaked) {
                    killEdges = controlFlowGraph.getBasicBlockEdgesBySource(head);
                } else
                    killEdges = controlFlowGraph.getBasicBlockEdgesByDest(edge.getDestination());
                Iterator<BasicBlockEdge> k = killEdges.iterator();
                d = destEdges.iterator();
                while (k.hasNext()) {
                    BasicBlockEdge kill = k.next();
                    while (!kill.equals(edge)) {
                        edge = e.next();
                        backup++;
                    }
                    e.remove();
                    while (d.hasNext()) {
                        BasicBlockEdge dest = d.next();
                        e.add(new BasicBlockEdge(kill.getSource(), dest.getDestination(), "UNCONDITIONAL"));
                        e.previous();
                        e.add(new BasicBlockEdge(kill.getSource(), head, ": " + cond, "REPEAT"));
                        e.previous();
                        d.remove();
                    }
                    k.remove();
                    while (backup-- > 1) {
                        e.previous();
                    }
                }

                if (destEdges.size() > 0 || killEdges.size() > 0) {
                    logger.fatal("Error translating to MFSim");
                    logger.fatal(destEdges);
                    logger.fatal(killEdges);
                }
                continue;
            }

            conditionalGroup.add(edge);
            if (instructions.get(instructions.size() - 1).getInstruction() instanceof Output) {
                boolean stationary = false;
                for (Variable var : instructions.get(instructions.size()-1).getInstruction().getInputs().values()) {
                    if (var instanceof Instance && ((Instance) var).getIsStationary()) {
                        stationary = true;
                    }
                }
                if (stationary)
                    conditionalGroups.put(edge.getSource(), conditionalGroup);
                // do not add group
            } else
                conditionalGroups.put(edge.getSource(), conditionalGroup);
        }

    }

    public boolean containsLegitInstructions(List<InstructionNode> instructions) {
        for (InstructionNode i : instructions) {
            if (i instanceof SigmaInstruction || i instanceof PHIInstruction)
                continue;
            return true;
        }
        return false;
    }

    public String toString(String filename) {
        String ret = "NAME(" + filename + ")\n\n";

        for (MFSimSSADAG dag : dags.values()) {
            if (!(dag.getNodes().size() == 0))// !(dag.getTransferInNode().size() == 0 || dag.getTransferOutNode().size() == 0))
                ret += "DAG(" + dag.getName() + ")\n";
            else {
                String index = dag.getName().substring(dag.getName().lastIndexOf('G') + 1);
                conditionalGroups.remove(Integer.parseInt(index));
            }
        }
        ret += "\n";

        ret += "NUMCGS(" + conditionalGroups.size() + ")\n\n";

        int controlGroup = 0;
        for (Integer sourceBasicBlockID : conditionalGroups.keySet()) {
            MFSimSSADAG sourceBasicBlock = dags.get(sourceBasicBlockID);
            for (BasicBlockEdge edge : conditionalGroups.get(sourceBasicBlockID)) {
                MFSimSSADAG destinationBasicBlock = dags.get(edge.getDestination());
                if (edge.getCondition() == "UNCONDITIONAL")
                    ret += "COND(" + controlGroup + ", 1, " + sourceBasicBlock.getName() + ", 1 ," + destinationBasicBlock.getName() + ", " + getUnconditionalJump(sourceBasicBlock.getName());
                else {
                    String conditionalExpression = resolveExpression(destinationBasicBlock.getName(), edge, sourceBasicBlockID);
                    ret += "COND(" + controlGroup + ", 1, " + sourceBasicBlock.getName() + ", 1 ," + destinationBasicBlock.getName() + ", " + conditionalExpression;

                }
                ret += "\n";
                for (ArrayList<MFSimSSATransferOut> ttransferOut : sourceBasicBlock.getTransferOutNode().values()) {
                    for (MFSimSSATransferOut transferOut : ttransferOut) {
                        for (ArrayList<MFSimSSATransferIn> ttransferIn : destinationBasicBlock.getTransferInNode().values()) {
                            for (MFSimSSATransferIn transferIn : ttransferIn) {
                                if (transferOut.getTransferedSymbol().equals(transferIn.getTransferedSymbol())) {
                                    ret += "TD(" + sourceBasicBlock.getName() + ", " + transferOut.getID() + ", " + destinationBasicBlock.getName() + ", " + transferIn.getID() + ")\n";
                                }
                            }
                        }
                    }
                }
            }

            controlGroup++;
            ret += "\n\n";
        }

        return ret;
    }


    public void toFile(String filename) {
        String cfgFileName = filename + ".cfg";
        BufferedWriter bw = null;
        try {
            File file = new File(cfgFileName);
            if (!file.exists()) {
                file.createNewFile();
            }
            FileWriter fw = new FileWriter(file);
            bw = new BufferedWriter(fw);
            bw.write(this.toString(cfgFileName));
        } catch (IOException ioe) {
            logger.fatal("IOException occurred when writing the cfg file for " + filename);
            logger.fatal(ioe.getMessage());
        } finally {
            try {
                if (bw != null)
                    bw.close();
            } catch (Exception ex) {
                logger.error("Error in closing the BufferedWriter" + ex);
            }
        }

        for (MFSimSSADAG dag : this.dags.values()) {
            String dagFileName = filename + "_" + dag.getName() + ".dag";
            String dagContents = dag.toString();
            try {

                File file = new File(dagFileName);


                if (!file.exists()) {
                    file.createNewFile();
                }

                FileWriter fw = new FileWriter(file);
                bw = new BufferedWriter(fw);
                bw.write(dagContents);
            } catch (IOException ioe) {
                logger.fatal(dagFileName + ": IOException");
                ioe.getStackTrace();
            } finally {
                try {
                    if (bw != null)
                        bw.close();
                } catch (Exception ex) {
                    logger.error("Error in closing the BufferedWriter" + ex);
                }
            }
        }
    }

    //Either a repeat expression, or a conditional on a sensor reading
    private String resolveExpression(String destName, BasicBlockEdge edge, Integer bbID) {
        Integer expressionID = this.uniqueIDGen.getNextID();
        String ret = expressionID + ")\nEXP(" + expressionID;
        logger.warn(edge + "type: " + edge.getType());
        if (edge.getType().equals("repeat")) {
            ret += ", RUN_COUNT, LT, " + dags.get(bbID).getName() + ", " + edge.getCondition() + ")\n";
        } else { // sensor reading control flow
            MFSimSSADAG dag = dags.get(bbID);
            Integer nodeID = 0;
            for (MFSimSSANode node : dag.getNodes().values()) {
                nodeID = node.getID();
            }
            String theDigits = CharMatcher.DIGIT.retainFrom(edge.getConditional().getRightOperand());

            ret += ", ONE_SENSOR, "
                    + edge.getMFSimConditional(edge.getConditional()) + ", "
                    + dag.getName() + ", "
                    + nodeID.toString() + ", "
                    + theDigits + ")\n";
        }
        return ret;
    }


    private String getUnconditionalJump(String Source) {
        Integer expressionID = this.uniqueIDGen.getNextID();
        String ret = expressionID + ")\nEXP(" + expressionID + ", TRUE, UNCOND, " + Source + ")\n";

        return ret;
    }
}