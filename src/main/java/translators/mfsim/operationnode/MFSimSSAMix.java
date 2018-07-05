package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Combine;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAMix extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer numMix;
    private Long time;

    public MFSimSSAMix(Integer id, Combine mixNode) {
        super(id, OperationClassifier.MIX, mixNode.getName());
        numMix = mixNode.getInputsAsList().size();
        time = getTime(mixNode);

    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.numMix + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
