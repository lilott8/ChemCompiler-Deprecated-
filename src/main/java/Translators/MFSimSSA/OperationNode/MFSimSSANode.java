package Translators.MFSimSSA.OperationNode;

import Translators.MFSimSSA.MFSimSSATranslator;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 10/28/16.
 */
public abstract class MFSimSSANode {
    protected enum OperationClassifier { COOL, DETECT, DILUTE, DISPENSE, HEAT, GENERAL, MIX, SPLIT, STORE, OUTPUT, TRANSFER_IN, TRANSFER_OUT;

        public String toString(){
            switch (this){
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

    protected Integer __nodeID;
    protected List<Integer> __successorIDs;
    protected OperationClassifier __opType;
    protected String __nodeName;

    public MFSimSSANode(Integer id, OperationClassifier type, String nodeName){
        this.__nodeID = id;
        this.__successorIDs = new ArrayList<Integer>();
        this.__opType = type;
        this.__nodeName = nodeName;
    }

    public void addSuccessor(Integer id){
        __successorIDs.add( id);

    }
    public Integer getID() { return __nodeID; }
}

