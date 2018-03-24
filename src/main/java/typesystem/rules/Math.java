package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import shared.variable.AssignedVariable;
import shared.variable.DefinedVariable;
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
@InferenceRule(ruleName = "math", ruleType = "term")
public class Math extends NodeAnalyzer {

    public Math(InferenceType type) {
        super(type, Math.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        Formula instruction = new Formula(InstructionType.MATH);

        // There can be only one input variable.
        Variable input = null;
        for (String s : node.getUse()) {
            input = new DefinedVariable(s);
            input.addTypingConstraints(getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        // There can be only one output variable.
        Variable output = null;
        for (String s : node.getDef()) {
            output = new AssignedVariable(s);
            output.addTypingConstraint(REAL);
            output.addTypingConstraint(NAT);
            instruction.addOutputVariable(output);
            addVariable(output);
        }

        addInstruction(instruction);
        return this;
    }
}
