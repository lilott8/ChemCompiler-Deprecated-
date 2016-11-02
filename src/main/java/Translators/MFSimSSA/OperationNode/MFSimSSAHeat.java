package Translators.MFSimSSA.OperationNode;

import executable.instructions.Heat;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAHeat extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Integer __time;
    public MFSimSSAHeat(Integer id, Heat heatNode){
        super(id, OperationClassifier.HEAT, heatNode.getName());

        //TODO:: extract time from Operation.
        logger.warn("Using template time for mix.");
        __time = 2;
    }
    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType +  ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
