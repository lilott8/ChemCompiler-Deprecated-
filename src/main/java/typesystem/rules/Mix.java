package typesystem.rules;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import chemical.epa.EpaManager;
import compilation.datastructures.node.InstructionNode;
import shared.variable.AssignedVariable;
import shared.variable.ManifestVariable;
import shared.variable.Variable;
import typesystem.Inference.InferenceType;
import typesystem.elements.Formula;

import static chemical.epa.ChemTypes.REAL;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * Mat = mix Mat with Mat ... for Real
 */
@InferenceRule(ruleName = "mix", ruleType = "instruction")
public class Mix extends NodeAnalyzer {

    public Mix(InferenceType type) {
        super(type, Mix.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {

        //Formula instruction = new Formula(node.getId(), InstructionType.MIX);
        Formula instruction = new Formula(InstructionType.MIX);

        Set<ChemTypes> groupings = new HashSet<>();

        Variable input = null;
        // Right hand side values (a = mix input with input)
        for (String in : node.getUse()) {
            input = new AssignedVariable(in);
            // If we have seen this before, we can just pull the old types.
            if (variables.containsKey(input.getVarName())) {
                input.addTypingConstraints(variables.get(input.getVarName()).getTypingConstraints());
            } else {
                // Otherwise we probably need to identify it.
                input.addTypingConstraints(identifier.identifyCompoundForTypes(input.getVarName()));
                logger.warn(input.getVarName() + " has no previous declarations...");
            }
            // Add the input to the instruction.
            instruction.addInputVariable(input);
            groupings.addAll(input.getTypingConstraints());
            addVariable(input);
        }

        Variable output = null;
        // If we have a def, we can get it.
        if (!node.getDef().isEmpty()) {
            // There will only ever be one def for a mix.
            for (String out : node.getDef()) {
                output = new ManifestVariable(out);
                output.addTypingConstraints(EpaManager.INSTANCE.lookUp(groupings));
            }
        } else {
            // Otherwise, get the last use.
            output = new ManifestVariable(input.getVarName());
            output.addTypingConstraints(EpaManager.INSTANCE.lookUp(groupings));
        }

        if (!output.getTypingConstraints().contains(ChemTypes.getMaterials())) {
            output.addTypingConstraint(ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
        }

        instruction.addOutputVariable(output);
        addVariable(output);

        // Get the properties of the instruction if they exist
        for (substance.Property p : node.getInstruction().getProperties()) {
            shared.variable.Property prop = new shared.variable.Property(Rule.createHash(p.toString()), "", p.getUnit().toString(), p.getQuantity());
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addProperty(prop);
        }

        addInstruction(instruction);
        // logger.trace("=======================");
        return this;
    }
}
