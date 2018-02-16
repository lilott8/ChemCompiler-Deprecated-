package typesystem.rules;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "nat", ruleType = "term")
public class Nat extends NodeAnalyzer {

    public Nat(InferenceType type) {
        super(type, Nat.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        throw new NotImplementedException();
    }
}
