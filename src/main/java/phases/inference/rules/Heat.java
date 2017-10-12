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
@InferenceRule(ruleName = "heat", ruleType = "instruction")
public class Heat extends NodeAnalyzer {

    public Heat(InferenceType type) {
        super(type, Heat.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        logger.info(node);
        logger.debug("InputSymbols: " + node.getInputSymbols());

        for(String s : node.getInputSymbols()) {
            this.addConstraints(s, identifier.identifyCompoundForTypes(s), ConstraintType.HEAT);
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.gatherConstraints(prop);
        }

        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraints(input, this.identifier.identifyCompoundForTypes(input), ConstraintType.HEAT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraints(input, this.identifier.identifyCompoundForTypes(input), ConstraintType.HEAT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(Rule.createHash(property.toString()), REAL, ConstraintType.NUMBER);
        return this;
    }
}
