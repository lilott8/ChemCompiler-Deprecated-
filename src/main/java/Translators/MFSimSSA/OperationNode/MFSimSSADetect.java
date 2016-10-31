package Translators.MFSimSSA.OperationNode;


import executable.instructions.Combine;
import executable.instructions.Detect;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADetect extends MFSimSSANode{
    private static final Logger logger = LogManager.getLogger(MFSimSSADetect.class);
    private Integer __numDetect;
    private Integer __time;

    public MFSimSSADetect(Integer id, Detect mixNode) {
        super(id, OperationClassifier.DETECT, mixNode.getName());
        __numDetect = mixNode.getInputs().size();

        //TODO:: extract time from Operation.
        logger.warn("Using template time for mix.");
        __time = 2;

    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__numDetect + ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
