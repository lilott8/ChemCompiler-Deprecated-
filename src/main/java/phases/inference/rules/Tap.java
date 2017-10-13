package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 10/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "tap", ruleType = "instruction")
public class Tap extends NodeAnalyzer {

    NodeAnalyzer mix = new Mix(Inference.InferenceType.INSTRUCTION);

    public Tap(Inference.InferenceType type) {
        super(type, Tap.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.mix.gatherAllConstraints(node);
    }

    @Override
    protected Rule gatherUseConstraints(String input) {
        return this.mix.gatherUseConstraints(input);
    }

    @Override
    protected Rule gatherDefConstraints(String input) {
        return this.mix.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.mix.gatherConstraints(property);
    }
}
