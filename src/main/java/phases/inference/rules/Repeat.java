package phases.inference.rules;

import org.apache.commons.lang3.StringUtils;

import compilation.datastructures.basicblock.BasicBlockEdge;
import phases.inference.satsolver.constraints.Constraint;
import typesystem.epa.ChemTypes;
import phases.inference.Inference.InferenceType;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "repeat", ruleType = "instruction", analyze = "edge")
public class Repeat extends EdgeAnalyzer {

    public Repeat(InferenceType type) {
        super(type, Repeat.class);
    }

    @Override
    public Rule gatherConstraints(BasicBlockEdge edge) {
        logger.trace(edge);

        // Split the condition into a string, get the operands and attempt to infer.
        for(String s : StringUtils.split(edge.getCondition())) {
            /*
             * If this isn't an operand, then we know it's a value, and can take that as is.
             * If it is an operand, we need to do some parsing to get at the values/terms.
             */
            if (!Rule.operands.contains(s)) {
                // We cannot define a variable here, so we can safely look
                // into the global constraints table.
                if (isNumeric(edge.getCondition())) {
                    if (isNaturalNumber(edge.getCondition())) {
                        this.addConstraint(createHash(edge.getConditional().getLeftOperand()), ChemTypes.NAT, ConstraintType.NUMBER);
                    } else {
                        this.addConstraint(createHash(edge.getConditional().getLeftOperand()), ChemTypes.REAL, ConstraintType.NUMBER);
                    }
                }
            } else {
                logger.error("No implementation for conditionals in repeat");
                //results.put("if", new HashSet<>());
                //results.get("if").add(Rule.NAT);
            }
            //logger.info(s);
        }
        return this;
    }


}
