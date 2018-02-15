package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference.InferenceType;
import typesystem.elements.Instruction;
import typesystem.elements.Term;
import shared.Variable;
import substance.Property;

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

        //Instruction instruction = new Instruction(node.getId(), InstructionType.OUTPUT);
        Instruction instruction = new Instruction(InstructionType.OUTPUT);

        Variable input = null;
        for (String s : node.getUse()) {
            input = new Term(s);
            input.addTypingConstraints(getTypingConstraints(input));
            instruction.addInputVariable(input);
            addVariable(input);
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
