package Translators.MFSimSSA.OperationNode;


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
        String ret = "NODE (" + this.__nodeID + ", " + this.__opType + ", "  + this.__nodeName + ")\n";

        for (Integer successor : this.__successorIDs) {
            ret += "EDGE (" + this.__nodeID + ", " + successor + ")\n";
        }
        return ret;
    }
}
