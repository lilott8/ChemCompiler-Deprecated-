package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "store", ruleType = "instruction")
public class Store extends NodeAnalyzer {

    private NodeAnalyzer output = new Output(InferenceType.INSTRUCTION);

    public Store(InferenceType type) {
        super(type, Store.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.output.gatherAllConstraints(node);
    }
}
