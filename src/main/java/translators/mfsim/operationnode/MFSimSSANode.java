package translators.mfsim.operationnode;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.List;

import executable.instructions.Instruction;
import substance.Property;
import substance.Units;

/**
 * Created by chriscurtis on 10/28/16.
 */
public abstract class MFSimSSANode {

    protected static final Logger logger = LogManager.getLogger(MFSimSSANode.class);
    protected Integer nodeID;
    protected List<Integer> successorIDs;
    protected OperationClassifier opType;
    protected String nodeName;

    public MFSimSSANode(Integer id, OperationClassifier type, String nodeName) {
        this.nodeID = id;
        this.successorIDs = new ArrayList<Integer>();
        this.opType = type;
        this.nodeName = nodeName;
    }

    public void addSuccessor(Integer id) {
        successorIDs.add(id);

    }

    public Integer getID() {
        return nodeID;
    }

    public String getName() {
        return nodeName;
    }

    long getTime(Instruction node) {
        for (Property p : node.getProperties()) {
            if (p.getUnit() instanceof Units.Time) {
                switch ((Units.Time) p.getUnit()) {
                    case DAY:
                        return (long) p.getQuantity() * 24 * 60 * 60 * 1000000;  //day to microsecond
                    case HOUR:
                        return (long) p.getQuantity() * 60 * 60 * 1000000; //hour to microsecond
                    case MINUTE:
                        return (long) p.getQuantity() * 60 * 1000000; //minute to microsecond
                    case SECOND:
                        return (long) p.getQuantity() * 1000000; //second to microsecond
                    case MILLISECOND:
                        return (long) p.getQuantity() * 1000;
                    case MICROSECOND:
                        return (long) p.getQuantity();
                    default:
                        logger.warn("Using template time.");
                }
            }
        }
        return 2;  //template time
    }

    protected enum OperationClassifier {
        COOL, DETECT, DILUTE, DISPENSE, HEAT, GENERAL, MIX, SPLIT, STORE, OUTPUT, TRANSFER_IN, TRANSFER_OUT;

        public String toString() {
            switch (this) {
                case COOL:
                    return "COOL";
                case DETECT:
                    return "DETECT";
                case DILUTE:
                    return "DILUTE";
                case DISPENSE:
                    return "DISPENSE";
                case HEAT:
                    return "HEAT";
                case GENERAL:
                    return "GENERAL";
                case MIX:
                    return "MIX";
                case SPLIT:
                    return "SPLIT";
                case STORE:
                    return "STORAGE";
                case OUTPUT:
                    return "OUTPUT";
                case TRANSFER_IN:
                    return "TRANSFER_IN";
                case TRANSFER_OUT:
                    return "TRANSFER_OUT";
                default:
                    return "UNKNOWN_OPERATION";
            }
        }
    }

}

