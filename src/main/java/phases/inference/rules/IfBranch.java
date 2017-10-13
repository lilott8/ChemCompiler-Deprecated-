package phases.inference.rules;

import org.apache.commons.lang3.StringUtils;

import compilation.datastructures.InstructionNode;
import compilation.datastructures.basicblock.BasicBlockEdge;
import phases.inference.Inference.InferenceType;
import phases.inference.satsolver.constraints.Constraint;
import substance.Property;
import typesystem.epa.ChemTypes;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "if", ruleType = "instruction", analyze = "edge")
public class IfBranch extends EdgeAnalyzer {

    public IfBranch(InferenceType type) {
        super(type, IfBranch.class);
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
