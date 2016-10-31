package Translators.MFSimSSA.OperationNode;

import executable.instructions.Combine;
import executable.instructions.Split;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSASplit extends MFSimSSANode{
    public static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer __numOutput;
    private Integer __time;

    public MFSimSSASplit(Integer id, Split splitNode) {
        super(id, OperationClassifier.SPLIT, splitNode.getName());
        __numOutput = splitNode.getInputs().size();

        //TODO:: extract time from Operation.
        logger.warn("Using template time for mix.");
        __time = 2;

    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__numOutput + ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
