package translators.mfsim.operationnode;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSATransferOut extends MFSimSSANode {
    private static final Logger logger = LogManager.getLogger(MFSimSSATransferOut.class);
    String transferedSymbol;

    public MFSimSSATransferOut(Integer id, String name, String symbol) {
        super(id, OperationClassifier.TRANSFER_OUT, name);
        this.transferedSymbol = symbol;
    }


    public String toString() {
        String ret = "NODE (" + this.nodeID + ", " + this.opType + ", " + this.nodeName + ")\n";

        for (Integer successor : this.successorIDs) {
            ret += "EDGE (" + this.nodeID + ", " + successor + ")\n";
        }
        return ret;
    }

    public String getTransferedSymbol() {
        return transferedSymbol;
    }
}
