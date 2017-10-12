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

    private NodeAnalyzer output = new Output(InferenceType.INSTRUCTION);

    public Store(InferenceType type) {
        super(type, Store.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.output.gatherAllConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return this.output.gatherUseConstraints(input);
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this.output.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.output.gatherConstraints(property);
    }
}
