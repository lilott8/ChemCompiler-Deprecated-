package phases.inference.rules;

import phases.inference.satsolver.Solver;

import CompilerDataStructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "detect", ruleType = "term")
public class Detect extends Rule {

    public Detect(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return super.gatherConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, MAT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, REAL);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(CONST, REAL);
        return this;
    }
}
