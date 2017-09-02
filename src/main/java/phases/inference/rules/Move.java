package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * move is a synonym of mix.
 */
@InferenceRule(ruleName = "move", ruleType = "instruction")
public class Move extends NodeAnalyzer {

    private NodeAnalyzer mix = new Mix(InferenceType.INSTRUCTION);

    public Move(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.mix.gatherAllConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return this.mix.gatherUseConstraints(input);
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this.mix.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.mix.gatherConstraints(property);
    }
}
