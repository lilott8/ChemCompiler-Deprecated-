package typesystem.rules;

import org.apache.commons.lang3.StringUtils;

import compilation.datastructures.basicblock.BasicBlockEdge;
import typesystem.Inference.InferenceType;
import typesystem.elements.Instruction;
import typesystem.elements.Term;
import shared.Variable;

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
        //Instruction instruction = new Instruction(edge.getId(), InstructionType.BRANCH);
        Instruction instruction = new Instruction(InstructionType.BRANCH);

        Variable output = new Term(Rule.createHash(edge.getConditional().toString()));
        output.addTypingConstraint(NAT);

        Variable left;
        if (isNumeric(edge.getConditional().getLeftOperand())) {
            left = new Term(Rule.createHash(edge.getConditional().getLeftOperand()));
        } else {
            left = new Term(edge.getConditional().getLeftOperand());
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
                right = new Term(Rule.createHash(edge.getConditional().getRightOperand()));
            } else {
                right = new Term(edge.getConditional().getRightOperand());
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
