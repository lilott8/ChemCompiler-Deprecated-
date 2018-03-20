package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAGeneral extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSAGeneral.class);

    public MFSimSSAGeneral(Integer id, String name) {
        super(id, OperationClassifier.GENERAL, name);

    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
