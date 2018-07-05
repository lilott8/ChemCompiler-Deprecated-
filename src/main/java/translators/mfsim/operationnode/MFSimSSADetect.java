package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Detect;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADetect extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSADetect.class);
    private Integer numDetect;
    private Long time;

    public MFSimSSADetect(Integer id, Detect detectNode) {
        super(id, OperationClassifier.DETECT, detectNode.getName());
        numDetect = detectNode.getInputs().size();

        Long x = getTime(detectNode);
        if (x != (long)2)
            logger.info("Detection for " + getTime(detectNode) + " seconds reduced to 2 " +
                    "seconds, assuming readings are ascertainable in a very short period of time from a physical sensor.");
        //time = getTime(detectNode);
        time = (long)2;
    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.numDetect + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
