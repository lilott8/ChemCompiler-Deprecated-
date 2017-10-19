package translators.mfsim.operationnode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADispense extends MFSimSSANode {
    public static final Logger logger = LogManager.getLogger(MFSimSSADispense.class);

    private String chemical;
    private Integer units;

    public MFSimSSADispense(Integer id, String name, String chemical, Integer amount) {
        super(id, OperationClassifier.DISPENSE, name);
        chemical = chemical;
        units = amount;

    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.chemical + ", " + units + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }

}
