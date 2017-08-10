package Phases.Inference.Rules;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "repeat", ruleType = "instruction")
public class While extends Rule {

    public While(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherConstraints(InstructionNode node) {
        return null;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, NAT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this;
    }
}
