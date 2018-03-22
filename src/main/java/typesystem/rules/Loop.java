package typesystem.rules;

import compilation.datastructures.basicblock.BasicBlockEdge;
import typesystem.Inference;

/**
 * @created: 3/21/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "loop", ruleType = "instruction", analyze = "edge")
public class Loop extends EdgeAnalyzer {
    private IfBranch branch = new IfBranch(Inference.InferenceType.INSTRUCTION);

    public Loop(Inference.InferenceType type) {
        super(type, Loop.class);
    }

    @Override
    public Rule gatherConstraints(BasicBlockEdge edge) {
        return this.branch.gatherConstraints(edge);
    }

}
