package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Output;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAOutput extends MFSimSSANode{
    private static final Logger logger = LogManager.getLogger(MFSimSSAOutput.class);
    private String __sink;

    public MFSimSSAOutput(Integer id, Output outputNode) {
        super(id, OperationClassifier.OUTPUT, outputNode.getName());

        for(String output: outputNode.getOutputs().keySet()){
            __sink = output;
        }
    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__sink +  ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
