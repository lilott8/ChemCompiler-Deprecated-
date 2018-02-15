package typesystem.rules;

import compilation.datastructures.basicblock.BasicBlockEdge;
import typesystem.Inference.InferenceType;


/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "elseif", ruleType = "instruction", analyze = "edge")
public class ElseIfBranch extends EdgeAnalyzer {

    public ElseIfBranch(InferenceType type) {
        super(type, ElseIfBranch.class);
    }

    private IfBranch branch = new IfBranch(InferenceType.INSTRUCTION);

    @Override
    public Rule gatherConstraints(BasicBlockEdge edge) {
        return this.branch.gatherConstraints(edge);
    }
}
