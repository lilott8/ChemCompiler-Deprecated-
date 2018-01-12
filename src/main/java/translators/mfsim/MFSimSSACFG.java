package translators.mfsim;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.BasicBlockEdge;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.node.InstructionNode;
import compilation.datastructures.ssa.StaticSingleAssignment;
import executable.instructions.Output;
import translators.mfsim.operationnode.MFSimSSANode;
import translators.mfsim.operationnode.MFSimSSATransferIn;
import translators.mfsim.operationnode.MFSimSSATransferOut;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSACFG{
    private static final Logger logger = LogManager.getLogger(MFSimSSACFG.class);

    private MFSimSSATranslator.IDGen uniqueIDGen;
    private Map<Integer, MFSimSSADAG> dags;
    private Map<Integer, List<BasicBlockEdge>> conditionalGroups;


    public MFSimSSACFG(CFG controlFlowGraph, MFSimSSATranslator.IDGen uniqueID){
        uniqueIDGen = uniqueID;
        dags = new LinkedHashMap<Integer, MFSimSSADAG>();
        conditionalGroups = new LinkedHashMap<Integer, List<BasicBlockEdge>>();

        for(BasicBlock bb : controlFlowGraph.getBasicBlocks().values()){
            MFSimSSADAG dag = new MFSimSSADAG(bb, uniqueID, ((StaticSingleAssignment) controlFlowGraph).getVariableStack());
            dags.put(bb.getId(), dag);
            logger.info(dag);
        }
        for(BasicBlockEdge edge: controlFlowGraph.getBasicBlockEdges()){
            List<BasicBlockEdge> conditionalGroup;

            if (conditionalGroups.containsKey(edge.getSource())) {
                conditionalGroup = conditionalGroups.get(edge.getSource());
            } else {
                conditionalGroup = new ArrayList<BasicBlockEdge>();
            }
            conditionalGroup.add(edge);
            List<InstructionNode> instructions = controlFlowGraph.getBasicBlock(edge.getSource()).getInstructions();
            if (instructions.get(instructions.size()-1).getInstruction() instanceof Output) {
                // do not add group
            }
            else
                conditionalGroups.put(edge.getSource(), conditionalGroup);
        }

    }

    public String toString(String filename){
        String ret=  "NAME(" + filename + ")\n\n";

        for (MFSimSSADAG dag : dags.values()) {
            if (!(dag.getNodes().size() == 0 && dag.getTransferInNode().size() == 0 && dag.getTransferOutNode().size() == 0))
                ret += "DAG("+ dag.getName() + ")\n";
            else {
                String index = dag.getName().substring(dag.getName().lastIndexOf('G')+1);
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
                if(edge.getCondition() == "UNCONDITIONAL")
                    ret+="COND("+ controlGroup + ", 1, " + sourceBasicBlock.getName() + ", 1 ," + destinationBasicBlock.getName()+ ", " + getUnconditionalJump(sourceBasicBlock.getName());
                else {
                    String conditionalExpression = resolveExpression(destinationBasicBlock.getName(), edge, sourceBasicBlockID);
                    ret += "COND("+ controlGroup + ", 1, " + sourceBasicBlock.getName() + ", 1 ," + destinationBasicBlock.getName() + ", " + conditionalExpression;

                }
                ret+="\n";
                for(ArrayList<MFSimSSATransferOut> ttransferOut: sourceBasicBlock.getTransferOutNode().values()){
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
            ret +="\n\n";
        }

        return ret;
    }


    public void toFile(String filename){
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
        }
        catch(IOException ioe){
            logger.fatal("IOException occured when writing the cfg file for " + filename);
            logger.fatal(ioe.getStackTrace());
        }
        finally {
            try{
                if(bw!=null)
                    bw.close();
            }catch(Exception ex){
                logger.error("Error in closing the BufferedWriter"+ex);
            }
        }

        for (MFSimSSADAG dag : this.dags.values()) {
            String dagFileName  = filename + "_" + dag.getName() + ".dag";
            String dagContents = dag.toString();
            try {

                File file = new File(dagFileName);


                if (!file.exists()) {
                    file.createNewFile();
                }

                FileWriter fw = new FileWriter(file);
                bw = new BufferedWriter(fw);
                bw.write(dagContents);
            }
            catch(IOException ioe){
                logger.fatal(dagFileName + ": IOException");
                logger.fatal(ioe.getStackTrace());
            }
            finally {
                try{
                    if(bw!=null)
                        bw.close();
                }catch(Exception ex){
                    logger.error("Error in closing the BufferedWriter"+ex);
                }
            }
        }
    }

    private String resolveExpression(String destName, BasicBlockEdge edge, Integer bbID){
        Integer expressionID = this.uniqueIDGen.getNextID();
        String ret = expressionID + ")\nEXP(" + expressionID ;
        if (edge.getType().toString().equals("repeat")) {
            ret += ", RUN_COUNT, LT, " + destName + ", " + edge.getCondition() + ")\n";
        }
        else if (false/*edge is while*/) {

        }
        else if (edge.getType().toString().equals("lte")){
            MFSimSSADAG dag = dags.get(bbID);
            Integer nodeID = 0;
            for (MFSimSSANode node : dag.getNodes().values()) {
                nodeID = node.getID();
            }
            ret += ", ONE_SENSOR, LoE, " + nodeID.toString() + "," +
                    edge.getCondition().substring((edge.getCondition().lastIndexOf("=")+1)) +")\n";
            logger.warn("Hard-coding ONE_SENSOR");
        }
        else {
            ret += ", <INSERT CONDITION HERE>)\n";
        }
        return ret;

    }
    private String getUnconditionalJump(String Source) {
        Integer expressionID = this.uniqueIDGen.getNextID();
        String ret =  expressionID + ")\nEXP("+ expressionID +", TRUE, UNCOND, " + Source +")\n";

        return ret;
    }
}