package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "dispense", ruleType = "instruction")
public class Dispense extends NodeAnalyzer {

    public Dispense(Inference.InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this;
    }
}
