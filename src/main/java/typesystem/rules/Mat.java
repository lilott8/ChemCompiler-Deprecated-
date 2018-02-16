package typesystem.rules;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "declaration", ruleType = "term")
public class Mat extends NodeAnalyzer {

    public Mat(InferenceType type) {
        super(type, Mat.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        throw new NotImplementedException();
    }

}
