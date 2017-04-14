package Translators.MFSimSSA.OperationNode;

import executable.instructions.Combine;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADilute extends MFSimSSANode{
    public static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer __numMix;
    private Long __time;

    public MFSimSSADilute(Integer id, Combine diluteNode) {
        super(id, OperationClassifier.DILUTE, diluteNode.getName());
        __numMix = diluteNode.getInputs().size();
        __time = getTime(diluteNode, logger);
    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__numMix + ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
