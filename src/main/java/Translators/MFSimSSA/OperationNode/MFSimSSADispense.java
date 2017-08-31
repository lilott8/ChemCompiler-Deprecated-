package Translators.MFSimSSA.OperationNode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSADispense extends MFSimSSANode {
    public static final Logger logger = LogManager.getLogger(MFSimSSADispense.class);

    private String __chemical;
    private Integer __units;

    public MFSimSSADispense(Integer id, String name, String chemical, Integer amount) {
        super(id, OperationClassifier.DISPENSE, name);
        __chemical = chemical;
        __units = amount;

    }

    public String toString() {
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", " + this.__chemical + ", " + __units + ", " + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }

}
