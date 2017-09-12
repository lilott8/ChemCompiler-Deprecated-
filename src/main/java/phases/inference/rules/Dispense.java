package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "dispense", ruleType = "term")
public class Dispense extends NodeAnalyzer {

    NodeAnalyzer assign = new Assign(Inference.InferenceType.TERM);

    public Dispense(Inference.InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.assign.gatherAllConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return this.assign.gatherUseConstraints(input);
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this.assign.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.gatherConstraints(property);
    }
}
