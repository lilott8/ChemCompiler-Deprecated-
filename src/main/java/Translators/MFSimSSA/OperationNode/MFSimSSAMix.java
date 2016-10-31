package Translators.MFSimSSA.OperationNode;


import executable.instructions.Combine;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAMix extends MFSimSSANode{
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer __numMix;
    private Integer __time;

    public MFSimSSAMix(Integer id, Combine mixNode) {
        super(id, OperationClassifier.MIX, mixNode.getName());
        __numMix = mixNode.getInputs().size();

        //TODO:: extract time from Operation.
        logger.warn("Using template time for mix.");
        __time = 2;

    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__numMix + ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
