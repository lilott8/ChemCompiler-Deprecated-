package phases.inference.rules;

import java.util.HashSet;
import java.util.Set;

import compilation.datastructures.node.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import substance.Property;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;

import static typesystem.epa.ChemTypes.REAL;

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

        Instruction instruction = new Instruction(node.getId(), InstructionType.MIX);

        Set<ChemTypes> groupings = new HashSet<>();

        Variable input = null;
        // Right hand side values (a = mix input with input)
        for (String in : node.getUse()) {
            input = new Term(in);
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

        Variable output;
        // If we have a def, we can get it.
        if (!node.getDef().isEmpty()) {
            // There will only ever be one def for a mix.
            for (String out : node.getDef()) {
                output = new Term(out);
                output.addTypingConstraints(EpaManager.INSTANCE.lookUp(groupings));
                instruction.addOutputVariable(output);
                addVariable(output);
            }
        } else {
            // Otherwise, get the last use.
            output = new Term(input.getVarName());
            output.addTypingConstraints(EpaManager.INSTANCE.lookUp(groupings));
            instruction.addOutputVariable(output);
            addVariable(output);
        }

        // Get the properties of the instruction if they exist
        for (Property p : node.getInstruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        // logger.trace("=======================");
        return this;
    }
}
