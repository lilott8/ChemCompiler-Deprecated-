package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import shared.properties.Property;
import shared.properties.Volume;
import shared.variable.ManifestVariable;
import shared.variable.Variable;
import typesystem.Inference.InferenceType;
import typesystem.elements.Formula;

import static chemical.epa.ChemTypes.REAL;

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

        //Formula instruction = new Formula(node.getId(), InstructionType.OUTPUT);
        Formula instruction = new Formula(InstructionType.OUTPUT);

        Variable input = null;
        for (String s : node.getUse()) {
            input = new ManifestVariable(s);
            input.addTypingConstraints(this.getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        for (substance.Property p : node.getInstruction().getProperties()) {
            Property prop = new Volume(Rule.createHash(p.toString()), p.getUnit().toString(), p.getQuantity());
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addProperty(prop);
        }

        addInstruction(instruction);
        return this;
    }
}
