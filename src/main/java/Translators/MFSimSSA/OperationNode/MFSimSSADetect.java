package Translators.MFSimSSA.OperationNode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Detect;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADetect extends MFSimSSANode{
    private static final Logger logger = LogManager.getLogger(MFSimSSADetect.class);
    private Integer __numDetect;
    private Long __time;

    public MFSimSSADetect(Integer id, Detect detectNode) {
        super(id, OperationClassifier.DETECT, detectNode.getName());
        __numDetect = detectNode.getInputs().size();

        __time = getTime(detectNode);

    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__numDetect + ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
