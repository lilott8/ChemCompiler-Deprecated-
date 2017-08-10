package Phases.Inference.Rules;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "if", ruleType = "instruction")
public class IfBranch extends Rule {

    public IfBranch(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherConstraints(InstructionNode node) {
        return null;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, NAT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return null;
    }
}
