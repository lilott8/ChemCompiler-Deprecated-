package typesystem.rules;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import chemical.identification.IdentifierFactory;
import compilation.datastructures.node.InstructionNode;
import shared.properties.Property;
import shared.properties.Time;
import shared.variable.NamedVariable;
import shared.variable.ManifestVariable;
import shared.variable.Variable;
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
            input = new NamedVariable(s);
            Set<ChemTypes> set = new HashSet<>();
            set.addAll(this.getTypingConstraints(input));
            if (set.isEmpty()) {
                input.addTypingConstraints(IdentifierFactory.getIdentifier().identifyCompoundForTypes(input.getName()));
            } else {
                input.addTypingConstraints(set);
            }
            input.addTypingConstraints(this.getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        // There can be only one output variable.
        Variable output = null;
        for (String s : node.getDef()) {
            output = new ManifestVariable(s);
            output.addTypingConstraint(REAL);
            instruction.addOutputVariable(output);
            addVariable(output);
        }

        for (substance.Property p : node.getInstruction().getProperties()) {
            Property prop = new Time(Rule.createHash(p.toString()), p.getUnit().toString(), p.getQuantity());
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addProperty(prop);
        }
        addInstruction(instruction);

        return this;
    }
}
