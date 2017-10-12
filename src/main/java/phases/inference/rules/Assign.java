package phases.inference.rules;

import java.util.Set;

import compilation.datastructures.InstructionNode;
import errors.ChemTrailsException;
import typesystem.epa.ChemTypes;
import phases.inference.Inference.InferenceType;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 */

@InferenceRule(ruleName = "assign", ruleType = "term")
public class Assign extends NodeAnalyzer {

    public Assign(InferenceType type) {
        super(type, Assign.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        if (this.config.isDebug()) {
             logger.trace(node);
             logger.trace("Input: " + node.getInputSymbols());
             logger.trace("Output: " + node.getOutputSymbols());
        }

        // Output Symbol        Input Symbol
        // Allyl Ethyl Ether = C=CCOC1=CC=CC=C1
        // TODO: converge the add constraints and identify compound.
        this.addConstraints(node.getOutputSymbols().get(0), this.identifier.identifyCompoundForTypes(node.getInputSymbols().get(0)), ConstraintType.ASSIGN);
        //this.addConstraints(node.getOutputSymbols().get(0), this.identifier.identifyCompound(node.getInputSymbols().get(0)));
        //logger.trace("Inferred Constraints: " + constraints.get(node.getOutputSymbols().get(0)));

        //logger.trace("=======================");

        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        if (isNumeric(input)) {
            this.addConstraint(input, isRealNumber(input) ? ChemTypes.REAL : ChemTypes.NAT, ConstraintType.NUMBER);
        } else {
            this.addConstraints(input, this.identifier.identifyCompoundForTypes(input), ConstraintType.ASSIGN);
        }
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this;
    }
}
