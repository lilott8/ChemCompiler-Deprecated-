package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

import static typesystem.epa.ChemTypes.MAT;
import static typesystem.epa.ChemTypes.REAL;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "detect", ruleType = "term")
public class Detect extends NodeAnalyzer {

    public Detect(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return super.gatherConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, MAT, ConstraintType.DETECT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, REAL, ConstraintType.NUMBER);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(CONST, REAL, ConstraintType.NUMBER);
        return this;
    }
}
