package typesystem.rules;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "math", ruleType = "term")
public class Math extends NodeAnalyzer {

    public Math(InferenceType type) {
        super(type, Math.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        throw new NotImplementedException();
        // return this;
    }
}
