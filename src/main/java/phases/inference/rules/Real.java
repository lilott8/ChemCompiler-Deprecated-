package phases.inference.rules;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "real", ruleType = "term")
public class Real extends NodeAnalyzer {

    public Real(InferenceType type) {
        super(type, Real.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        throw new NotImplementedException();
    }
}
