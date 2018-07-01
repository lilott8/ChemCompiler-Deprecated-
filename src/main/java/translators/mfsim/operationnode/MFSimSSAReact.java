package translators.mfsim.operationnode;

import executable.instructions.Heat;
import executable.instructions.React;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by tysonloveless on 10/28/17.
 */
public class MFSimSSAReact extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Long time;

    public MFSimSSAReact(Integer id, React reactNode) {
        super(id, OperationClassifier.REACT, reactNode.getName());
        time = getTime(reactNode);
    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
