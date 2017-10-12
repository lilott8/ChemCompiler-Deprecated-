package phases.inference.rules;

import java.util.HashSet;

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

        for (String input : node.getInputSymbols()) {
            this.addConstraints(input, this.identifier.identifyCompoundForTypes(input), ConstraintType.DETECT);
        }

        for (String output : node.getOutputSymbols()) {
            this.addConstraint(output, REAL, ConstraintType.NUMBER);
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.gatherConstraints(prop);
        }

        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraints(input, this.identifier.identifyCompoundForTypes(input), ConstraintType.DETECT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, REAL, ConstraintType.NUMBER);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(Rule.createHash(property.toString()), REAL, ConstraintType.NUMBER);
        return this;
    }
}
