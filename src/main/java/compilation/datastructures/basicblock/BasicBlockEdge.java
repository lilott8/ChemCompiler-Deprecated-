package compilation.datastructures.basicblock;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.Serializable;

import static compilation.datastructures.basicblock.BasicBlockEdge.__type.eq;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.gt;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.gte;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.lt;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.lte;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.neq;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.repeat;
import static compilation.datastructures.basicblock.BasicBlockEdge.__type.un;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class BasicBlockEdge implements Serializable {
    private Integer __source;
    private Integer __destination;

//this still needs to be created.
    private String __condition;
    protected enum __type {un, repeat, lt, lte, gt, gte, eq, neq };
    protected String classification;
    private __type type;

    public static Logger logger = LogManager.getLogger(BasicBlockEdge.class);

    public BasicBlockEdge(Integer source, Integer destination, String condition) {
        __source = source;
        __destination = destination;
        __condition = condition;
        this.type = un;
        this.classification = "unknown";
    }

    public BasicBlockEdge(Integer source, Integer destination, String expression, String type) {
        __source = source;
        __destination = destination;
        __condition = evaluateCondition(expression, type);
        this.classification = StringUtils.lowerCase(type);
    }

    private String evaluateCondition(String expression, String type) {
        String ret = "";
        if (type.equals("REPEAT")) {
            this.type = repeat;
        }
        else if (type.equals("WHILE") || type.equals("IF")) {
            this.type = evaluateBoolean(expression);
        }
        else {
            logger.fatal("error evaluating loop");
        }
        switch (this.type) {
            case repeat:
                ret = expression.substring((expression.lastIndexOf(":")+2));
                break;
            default:
                ret = expression;
        }

        return ret;
    }

    private __type evaluateBoolean(String expression) {
        if (expression.contains("<=")) {
            return lte;
        }
        else if (expression.contains("<")) {
            return lt;
        }
        else if (expression.contains(">=")) {
            return gte;
        }
        else if (expression.contains(">")) {
            return gt;
        }
        else if (expression.contains("==")) {
            return eq;
        }
        else if (expression.contains("!=")) {
            return neq;
        }
        else {
            return un;
        }
    }

    public String getType() { return this.type.toString(); }

    public String toString() {
        return this.toString("");
    }
    public String toString(String indentBuffer) {
        return indentBuffer + __source.toString() + " -> " + __destination + " : " + evaluateBoolean(__condition) + "\t(" + getType() + ")";
    }

    public String getClassification() {
        return this.classification;
    }
    public Integer getSource() { return __source; }
    public Integer getDestination() {return __destination; }
    public String getCondition()  { return __condition; }
}
