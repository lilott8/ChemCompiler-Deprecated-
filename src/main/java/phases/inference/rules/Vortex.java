package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 8/31/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName="vortex", ruleType="instruction")
public class Vortex extends Rule {

    Mix mix = new Mix(Inference.InferenceType.INSTRUCTION);

    public Vortex(Inference.InferenceType type) {
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
