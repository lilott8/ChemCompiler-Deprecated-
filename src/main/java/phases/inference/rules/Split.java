package phases.inference.rules;

import compilation.datastructures.node.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import substance.Property;

import static typesystem.epa.ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION;
import static typesystem.epa.ChemTypes.REAL;

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

        Instruction instruction = new Instruction(node.getId(), InstructionType.SPLIT);

        Variable input = null;
        for (String s : node.getUse()) {
            input = new Term(s);
            input.addTypingConstraints(getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        Variable output = null;
        for (String s : node.getDef()) {
            output = new Term(s);
            if (input == null) {
                // logger.warn("Input is null!?");
                output.addTypingConstraint(INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
            } else {
                output.addTypingConstraints(getTypingConstraints(input));
            }
            instruction.addOutputVariable(output);
            addVariable(output);
        }

        for (Property p : node.getInstruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        return this;
    }
}
