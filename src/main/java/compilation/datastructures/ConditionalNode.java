package compilation.datastructures;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Arrays;

import phases.inference.rules.Rule;

import static compilation.datastructures.basicblock.BasicBlockEdge.ConditionalType;

/**
 * @created: 10/11/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ConditionalNode {

    public static final Logger logger = LogManager.getLogger(ConditionalNode.class);

    private ConditionalType conditionalType;
    private String leftOperand = "";
    private String rightOperand = "";

    public ConditionalNode(ConditionalType condition, String operands) {
        this.conditionalType = condition;
        setOperands(operands);
    }

    private void setOperands(String condition) {
        String[] array = StringUtils.split(condition, this.conditionalType.toString());
        if (array.length == 2) {
            leftOperand = StringUtils.strip(array[0]);
            rightOperand = StringUtils.strip(array[1]);
            if (Rule.isNumeric(rightOperand)) {
                rightOperand = Rule.createHash(rightOperand);
            }
        } else {
            leftOperand = StringUtils.strip(array[0]);
        }

        if (Rule.isNumeric(leftOperand)) {
            leftOperand = Rule.createHash(leftOperand);
        }
    }

    public String getLeftOperand() {
        return this.leftOperand;
    }

    public String getRightOperand() {
        return this.rightOperand;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(this.leftOperand).append(" ").append(this.conditionalType.toString())
                .append(" ").append(this.rightOperand);
        return sb.toString();
    }

}
