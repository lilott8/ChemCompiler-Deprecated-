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
        // We are always guaranteed to have the left operand.
        this.addConstraint(edge.getConditional().getLeftOperand(), ChemTypes.REAL, Constraint.ConstraintType.BRANCH);
        // But we are not guaranteed to have
        if (!StringUtils.isEmpty(edge.getConditional().getRightOperand())) {
            this.addConstraint(edge.getConditional().getRightOperand(), ChemTypes.REAL, Constraint.ConstraintType.BRANCH);
        }
        return this;
    }


}
