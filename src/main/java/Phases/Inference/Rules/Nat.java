package Phases.Inference.Rules;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "nat", ruleType = "term")
public class Nat extends Rule {

    public Nat(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherConstraints(InstructionNode node) {
        return null;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return null;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return null;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return null;
    }
}
