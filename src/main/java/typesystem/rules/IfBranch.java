package typesystem.rules;

import org.apache.commons.lang3.StringUtils;

import compilation.datastructures.basicblock.BasicBlockEdge;
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

        Variable output = new shared.variable.Property(Rule.createHash(edge.getConditional().toString()));
        output.addTypingConstraint(NAT);
        addVariable(output);

        Variable left;
        if (isNumeric(edge.getConditional().getLeftOperand())) {
            left = new shared.variable.Property(Rule.createHash(edge.getConditional().getLeftOperand()));
        } else {
            left = new shared.variable.Property(edge.getConditional().getLeftOperand());
        }
        // We have to do this separately because if we don't have a typing,
        // Then it must be a real.
        if (variables.containsKey(left.getVarName())) {
            left.addTypingConstraints(variables.get(left.getVarName()).getTypingConstraints());
        } else {
            left.addTypingConstraint(REAL);
        }
        addVariable(left);

        instruction.addInputVariable(left);
        instruction.addOutputVariable(output);

        // But we are not guaranteed to have
        if (!StringUtils.isEmpty(edge.getConditional().getRightOperand())) {
            Variable right;
            if (isNumeric(edge.getConditional().getRightOperand())) {
                right = new shared.variable.Property(Rule.createHash(edge.getConditional().getRightOperand()));
            } else {
                right = new shared.variable.Property(edge.getConditional().getRightOperand());
            }
            // We have to do this separately because if we don't have a typing,
            // Then it must be a real.
            if (variables.containsKey(right.getVarName())) {
                right.addTypingConstraints(variables.get(right.getVarName()).getTypingConstraints());
            } else {
                right.addTypingConstraint(REAL);
            }
            instruction.addInputVariable(right);
            addVariable(right);
        }

        addInstruction(instruction);

        return this;
    }
}
