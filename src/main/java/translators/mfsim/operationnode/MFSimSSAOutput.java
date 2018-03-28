package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Output;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAOutput extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAOutput.class);
    private String sink;

    public MFSimSSAOutput(Integer id, Output outputNode) {
        super(id, OperationClassifier.OUTPUT, outputNode.getName());

        for (String output : outputNode.getOutputs().keySet()) {
            sink = output;
        }
    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.sink + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
