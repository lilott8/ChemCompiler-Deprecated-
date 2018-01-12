package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import executable.instructions.Store;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSAStorage extends MFSimSSANode{
    private static final Logger logger = LogManager.getLogger(MFSimSSAStorage.class);

    public MFSimSSAStorage(Integer id, Store storeNode) {
        super(id, OperationClassifier.STORE, storeNode.getName());

    }

    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
