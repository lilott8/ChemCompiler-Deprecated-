package phases.inference.rules;

import compilation.datastructures.node.InstructionNode;
import phases.inference.Inference;

/**
 * @created: 10/11/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "incubate", ruleType = "instruction")
public class Incubate extends NodeAnalyzer {

    private NodeAnalyzer heat = new Heat(Inference.InferenceType.INSTRUCTION);

    public Incubate(Inference.InferenceType type) {
        super(type, Incubate.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.heat.gatherAllConstraints(node);
    }
}
