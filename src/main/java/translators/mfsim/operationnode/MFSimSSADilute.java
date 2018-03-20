package translators.mfsim.operationnode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Combine;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADilute extends MFSimSSANode {
    public static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer numMix;
    private Long time;

    public MFSimSSADilute(Integer id, Combine diluteNode) {
        super(id, OperationClassifier.DILUTE, diluteNode.getName());
        numMix = diluteNode.getInputs().size();
        time = getTime(diluteNode);
    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.numMix + ", " + time + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
