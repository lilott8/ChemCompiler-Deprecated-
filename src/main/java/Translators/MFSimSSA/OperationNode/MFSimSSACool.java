package Translators.MFSimSSA.OperationNode;

import executable.instructions.Heat;
import executable.instructions.React;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSACool extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Long __time;

    public MFSimSSACool(Integer id, React reactNode) {
        super(id, OperationClassifier.COOL, reactNode.getName());
        __time = getTime(reactNode);
    }

    public MFSimSSACool(Integer id, Heat heatNode){
        super(id, OperationClassifier.COOL, heatNode.getName());
        __time = getTime(heatNode);
    }
    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + __time + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
