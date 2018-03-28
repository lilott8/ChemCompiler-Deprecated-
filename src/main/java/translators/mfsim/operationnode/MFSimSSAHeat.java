package translators.mfsim.operationnode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Heat;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAHeat extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Long time;

    public MFSimSSAHeat(Integer id, Heat heatNode) {
        super(id, OperationClassifier.HEAT, heatNode.getName());
        time = getTime(heatNode);
    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
