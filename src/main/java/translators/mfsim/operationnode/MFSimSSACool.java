package translators.mfsim.operationnode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Heat;
import executable.instructions.React;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSACool extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Long time;

    public MFSimSSACool(Integer id, React reactNode) {
        super(id, OperationClassifier.COOL, reactNode.getName());
        time = getTime(reactNode);
    }

    public MFSimSSACool(Integer id, Heat heatNode){
        super(id, OperationClassifier.COOL, heatNode.getName());
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
