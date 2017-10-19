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
public class Vortex extends NodeAnalyzer {

    NodeAnalyzer mix = new Mix(Inference.InferenceType.INSTRUCTION);

    public Vortex(Inference.InferenceType type) {
        super(type, Vortex.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.mix.gatherAllConstraints(node);
    }
}
