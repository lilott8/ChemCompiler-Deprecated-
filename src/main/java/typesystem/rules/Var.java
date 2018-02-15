package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "var", ruleType = "term")
public class Var extends NodeAnalyzer {

    private NodeAnalyzer assign = new Assign(InferenceType.TERM);

    public Var(InferenceType type) {
        super(type, Var.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.assign.gatherAllConstraints(node);
    }
}
