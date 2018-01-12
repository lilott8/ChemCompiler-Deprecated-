package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Detect;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADetect extends MFSimSSANode{
    private static final Logger logger = LogManager.getLogger(MFSimSSADetect.class);
    private Integer numDetect;
    private Long time;

    public MFSimSSADetect(Integer id, Detect detectNode) {
        super(id, OperationClassifier.DETECT, detectNode.getName());
        numDetect = detectNode.getInputs().size();

        time = getTime(detectNode);

    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.numDetect + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
