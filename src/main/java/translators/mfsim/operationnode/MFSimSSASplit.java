package translators.mfsim.operationnode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Split;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSASplit extends MFSimSSANode{
    public static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer numOutput;
    private Long time;

    public MFSimSSASplit(Integer id, Split splitNode) {
        super(id, OperationClassifier.SPLIT, splitNode.getName());
        numOutput = splitNode.getInputs().size();
        time = getTime(splitNode);

    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.numOutput + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
