package phases.inference.rules;

import java.util.HashSet;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;
import typesystem.identification.IdentifierFactory;

import static typesystem.epa.ChemTypes.REAL;

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

        logger.info("Uses: " + node.get_use());
        logger.info("Defs: " + node.get_def());

        Instruction instruction = new Instruction(node.ID(), Heat.class.getName());

        Variable input = null;
        // There is only ever one input.
        for (String s : node.get_use()) {
            input = new Term(s);
            input.addTypingConstraints(getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
        }

        // The output of the instruction is the same as the input.
        Variable output = input;
        instruction.addOutputVariable(output);
        addVariable(output);

        for (Property p : node.Instruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addInputVariable(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        return this;
    }
}
