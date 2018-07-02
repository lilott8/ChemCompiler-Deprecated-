package typesystem.rules;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import chemical.identification.IdentifierFactory;
import compilation.datastructures.node.InstructionNode;
import shared.variable.NamedVariable;
import shared.variable.ManifestVariable;
import shared.variable.Variable;
import typesystem.Inference.InferenceType;
import typesystem.elements.Formula;

import static chemical.epa.ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "split", ruleType = "instruction")
public class Split extends NodeAnalyzer {

    public Split(InferenceType type) {
        super(type, Split.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        /*
        logger.info(node);
        logger.info(node.getInstruction());
        logger.info(node.getInstruction());
        logger.info("Uses: " + node.getUse());
        logger.info("Defs: " + node.getDef());
        logger.info("Props: " + node.getInstruction().getProperties());
        logger.info(node.getDispenseSymbols());
        logger.info("=========================");
        */

        // Formula instruction = new Formula(node.getId(), InstructionType.SPLIT);
        Formula instruction = new Formula(InstructionType.SPLIT);
        Set<ChemTypes> outputTypes = new HashSet<>();

        Variable input = null;
        for (String s : node.getUse()) {
            input = new NamedVariable(s);
            input.addTypingConstraints(this.getTypingConstraints(input));
            if (!input.getTypingConstraints().contains(ChemTypes.getMaterials())) {
                input.addTypingConstraints(IdentifierFactory.getIdentifier().identifyCompoundForTypes(input.getName()));
            }
            // There shouldn't be multiple inputs, but if there are,
            // This will catch all the types and put them in it.
            outputTypes.addAll(input.getTypingConstraints());
            instruction.addInputVariable(input);
            addVariable(input);
        }

        Variable output = null;
        for (String s : node.getDef()) {
            output = new ManifestVariable(s);
            if (input == null) {
                // logger.warn("Input is null!?");
                output.addTypingConstraint(INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
            } else {
                output.addTypingConstraints(outputTypes);
            }
            instruction.addOutputVariable(output);
            addVariable(output);
        }

        /*for (Property p : node.getInstruction().getProperties()) {
            Property prop = new shared.properties.Property(Rule.createHash(p.toString()), this.propertyTypes);
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addVariable(prop);
        }*/

        addInstruction(instruction);
        return this;
    }
}
