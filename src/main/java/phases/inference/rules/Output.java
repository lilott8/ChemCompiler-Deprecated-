package phases.inference.rules;

import java.util.HashSet;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;
import substance.Property;

import static typesystem.epa.ChemTypes.MAT;
import static typesystem.epa.ChemTypes.REAL;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "output", ruleType = "instruction")
public class Output extends NodeAnalyzer {

    public Output(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        for(String s : node.getInputSymbols()) {
            this.addConstraints(s, new HashSet<>(), ConstraintType.OUTPUT);
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.gatherConstraints(prop);
        }

        return super.gatherConstraints(node);
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraints(input, new HashSet<>(), ConstraintType.OUTPUT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraints(input, new HashSet<>(), ConstraintType.OUTPUT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(Rule.createHash(property.toString()), REAL, ConstraintType.NUMBER);
        return this;
    }
}
