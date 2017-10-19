package phases.inference.rules;

import compilation.datastructures.basicblock.BasicBlockEdge;
import phases.inference.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "repeat", ruleType = "instruction", analyze = "edge")
public class Repeat extends EdgeAnalyzer {

    public Repeat(InferenceType type) {
        super(type, Repeat.class);
    }

    private IfBranch branch = new IfBranch(InferenceType.INSTRUCTION);

    @Override
    public Rule gatherConstraints(BasicBlockEdge edge) {
        return this.branch.gatherConstraints(edge);
    }


}
