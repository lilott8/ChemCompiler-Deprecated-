package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import shared.variable.AssignedVariable;
import shared.variable.Variable;
import substance.Property;
import typesystem.Inference.InferenceType;
import typesystem.elements.Formula;

import static chemical.epa.ChemTypes.REAL;

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

        //Formula instruction = new Formula(node.getId(), InstructionType.HEAT);
        Formula instruction = new Formula(InstructionType.HEAT);

        Variable input = null;
        // There is only ever one input.
        for (String s : node.getUse()) {
            input = new AssignedVariable(s);
            input.addTypingConstraints(this.getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        // The output of the instruction is the same as the input.
        Variable output = input;
        instruction.addOutputVariable(output);
        addVariable(output);

        for (Property p : node.getInstruction().getProperties()) {
            Variable prop = new shared.variable.Property(Rule.createHash(p.toString()), this.propertyTypes);
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        return this;
    }
}
