package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import shared.variable.AssignedVariable;
import shared.variable.DefinedVariable;
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
@InferenceRule(ruleName = "detect", ruleType = "term")
public class Detect extends NodeAnalyzer {

    public Detect(InferenceType type) {
        super(type, Detect.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {

        //Formula instruction = new Formula(node.getId(), InstructionType.DETECT);
        Formula instruction = new Formula(InstructionType.DETECT);

        // There can be only one input variable.
        Variable input = null;
        for (String s : node.getUse()) {
            input = new AssignedVariable(s);
            input.addTypingConstraints(getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        // There can be only one output variable.
        Variable output = null;
        for (String s : node.getDef()) {
            output = new DefinedVariable(s);
            output.addTypingConstraint(REAL);
            instruction.addOutputVariable(output);
            addVariable(output);
        }

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
