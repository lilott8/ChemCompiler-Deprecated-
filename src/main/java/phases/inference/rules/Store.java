package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

import static typesystem.epa.ChemTypes.MAT;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "store", ruleType = "instruction")
public class Store extends NodeAnalyzer {

    public Store(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return super.gatherConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, MAT, ConstraintType.STORE);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this;
    }
}
