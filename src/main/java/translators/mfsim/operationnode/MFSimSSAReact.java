package translators.mfsim.operationnode;

import executable.instructions.*;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import variable.Instance;

/**
 * Created by tysonloveless on 10/28/17.
 */
public class MFSimSSAReact extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAMix.class);
    private Long time;
    private Instance stationary;
    private String property; //numMix(mix), sinkName(drain), temperature(heat), numSensors(detect)
    private String subType;


    public MFSimSSAReact(Integer id, Instruction reactNode, Instance stationary) {
        super(id, OperationClassifier.REACT, reactNode.getName());
        time = getTime(reactNode);
        this.stationary = stationary;
        if (reactNode instanceof Combine) {
            property = String.valueOf((reactNode).getInputs().size());
            subType = "MIX";
        }
        else if (reactNode instanceof Output) {
            //property = reactNode.getOutputs().keySet().iterator().next();
            subType = "OUTPUT";
        }
        else if (reactNode instanceof Detect) {
            property = String.valueOf(reactNode.getInputs().size());
            subType = reactNode.getClassification();
        }
        else if (reactNode instanceof Heat) {
            property = String.valueOf(reactNode.getProperties().iterator().next().getQuantity());
            subType = "HEAT";
        }
        else if (reactNode instanceof React) {
            property = String.valueOf((reactNode).getInputs().size());
            subType = "MIX"; // assume a "react" means to mix a droplet with the stationary reagent
        }
    }


    public String toString() {
        // NODE(<id>, REACT, <time>, <nodeName>, <nodeType + [specifics]>, <stationaryName>)
        String ret = "NODE ("
                + this.nodeID + ", "
                + this.opType + ", "
                + this.time + ", "
                + this.nodeName + ", "
                + this.subType + ", ";

        if (this.property != null)
            ret += this.property + ", ";
        ret += this.stationary.getName() + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
