package typesystem.rules;

import org.apache.commons.lang3.StringUtils;

import compilation.datastructures.basicblock.BasicBlockEdge;
import shared.variable.Property;
import shared.variable.Variable;
import typesystem.Inference.InferenceType;
import typesystem.elements.Formula;

import static chemical.epa.ChemTypes.NAT;
import static chemical.epa.ChemTypes.REAL;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "if", ruleType = "instruction", analyze = "edge")
public class IfBranch extends EdgeAnalyzer {

    public IfBranch(InferenceType type) {
        super(type, IfBranch.class);
    }

    @Override
    public Rule gatherConstraints(BasicBlockEdge edge) {
        //Formula instruction = new Formula(edge.getId(), InstructionType.BRANCH);
        Formula instruction = new Formula(InstructionType.BRANCH);

        Property output = new Property(Rule.createHash(edge.getConditional().toString()), Property.CONDITIONAL, "", -1);
        output.addTypingConstraint(NAT);
        addProperty(output);

        Property left;
        if (isNumeric(edge.getConditional().getLeftOperand())) {
            left = new Property(Rule.createHash(edge.getConditional().getLeftOperand()), Property.CONDITIONAL, "", -1);
        } else {
            left = new Property(edge.getConditional().getLeftOperand(), Property.CONDITIONAL, "", -1);
        }
        // We have to do this separately because if we don't have a typing,
        // Then it must be a real.
        if (properties.containsKey(left.getName())) {
            left.addTypingConstraints(variables.get(left.getName()).getTypingConstraints());
        } else {
            left.addTypingConstraint(REAL);
        }
        addProperty(left);

        instruction.addProperty(left);
        instruction.addProperty(output);

        // But we are not guaranteed to have
        if (!StringUtils.isEmpty(edge.getConditional().getRightOperand())) {
            Property right;
            if (isNumeric(edge.getConditional().getRightOperand())) {
                right = new Property(Rule.createHash(edge.getConditional().getRightOperand()), Property.CONDITIONAL, "", -1);
            } else {
                right = new Property(edge.getConditional().getRightOperand(), Property.CONDITIONAL, "", -1);
            }
            // We have to do this separately because if we don't have a typing,
            // Then it must be a real.
            if (properties.containsKey(right.getName())) {
                right.addTypingConstraints(variables.get(right.getName()).getTypingConstraints());
            } else {
                right.addTypingConstraint(REAL);
            }
            instruction.addProperty(right);
            addProperty(right);
        }

        addInstruction(instruction);

        return this;
    }
}
