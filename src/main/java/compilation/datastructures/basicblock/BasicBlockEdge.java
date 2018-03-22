package compilation.datastructures.basicblock;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.Serializable;

import compilation.datastructures.node.ConditionalNode;

import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.eq;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.gt;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.gte;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.lt;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.lte;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.neq;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.repeat;
import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType.un;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class BasicBlockEdge implements Serializable {
    public static Logger logger = LogManager.getLogger(BasicBlockEdge.class);
    protected String classification;
    private Integer source;
    private Integer destination;
    //this still needs to be created.
    private String condition;
    private ConditionalType type;
    private ConditionalNode conditional;
    private int id;

    public BasicBlockEdge(Integer source, Integer destination, String condition) {
        this.source = source;
        this.destination = destination;
        this.condition = condition;
        this.id = source * destination;
        this.type = un;
        this.classification = "unknown";
        this.conditional = new ConditionalNode(this.type, this.condition);
    }

    public BasicBlockEdge(Integer source, Integer destination, String expression, String type) {
        this.source = source;
        this.destination = destination;
        condition = evaluateCondition(expression, type);
        this.id = source * destination;
        this.classification = StringUtils.lowerCase(type);
        this.conditional = new ConditionalNode(this.type, condition);
    }

    private String evaluateCondition(String expression, String type) {
        String ret = "";
        if (type.equals("REPEAT") || type.equals("LOOP")) {
            this.type = repeat;
        } else if (type.equals("WHILE") || type.equals("IF")) {
            this.type = evaluateBoolean(expression);
        }
        // TODO: validate the correctness of this.
        // added 2017-10-11
        else if (StringUtils.equalsIgnoreCase(type, "ELSEIF")) {
            this.type = evaluateBoolean(expression);
        } else {
            logger.fatal("error evaluating loop");
        }
        switch (this.type) {
            case repeat:
                ret = expression.substring((expression.lastIndexOf(":") + 2));
                break;
            default:
                ret = expression;
        }

        return ret;
    }

    public int getId() {
        return this.id;
    }

    private ConditionalType evaluateBoolean(String expression) {
        if (expression.contains("<=")) {
            return lte;
        } else if (expression.contains("<")) {
            return lt;
        } else if (expression.contains(">=")) {
            return gte;
        } else if (expression.contains(">")) {
            return gt;
        } else if (expression.contains("==")) {
            return eq;
        } else if (expression.contains("!=")) {
            return neq;
        } else {
            return un;
        }
    }

    public String getType() {
        return this.type.toString();
    }

    public String toString() {
        return this.toString("");
    }

    public String toString(String indentBuffer) {
        return indentBuffer + source.toString() + " -> " + destination + " : " + evaluateBoolean(condition) + "\t(" + getType() + ")";
    }

    public String getClassification() {
        return this.classification;
    }

    public int getSource() {
        return source;
    }

    public int getDestination() {
        return destination;
    }

    public String getCondition() {
        return condition;
    }

    public ConditionalNode getConditional() {
        return this.conditional;
    }

    public enum ConditionalType {
        un {
            public String toString() {
                return "";
            }
        },
        repeat {
            public String toString() {
                return " ";
            }
        },
        lt {
            public String toString() {
                return "<";
            }
        },
        lte {
            public String toString() {
                return "<=";
            }
        },
        gt {
            public String toString() {
                return ">";
            }
        },
        gte {
            public String toString() {
                return ">=";
            }
        },
        eq {
            public String toString() {
                return "==";
            }
        },
        neq {
            public String toString() {
                return "";
            }
        };

        public String toString(ConditionalType t) {
            switch (t) {
                default:
                case un:
                    return "";
                case repeat:
                    return " ";
                case lt:
                    return "<";
                case lte:
                    return "<=";
                case gt:
                    return ">";
                case gte:
                    return ">=";
                case eq:
                    return "==";
                case neq:
                    return "!=";
            }
        }
    }
}
