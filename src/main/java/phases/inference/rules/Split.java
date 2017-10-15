package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

import static typesystem.epa.ChemTypes.MAT;
import static typesystem.epa.ChemTypes.NAT;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "split", ruleType = "instruction")
public class Split extends NodeAnalyzer {

    public Split(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        logger.fatal("Using generic implementation for split!");

        Variable input = new Term(node.getInputSymbols().get(0));
        if (variables.containsKey(input.getVarName())) {
            input = variables.get(input.getVarName());
        }

        Instruction instruction = new Instruction(node.ID(), Split.class.getName());
        instruction.addInputVariable(input);
        for (String s : node.getOutputSymbols()) {
            Variable output = new Term(s);
            output.addTypingConstraints(input.getTypingConstraints());
            addVariable(output);
            instruction.addOutputVariable(output);
        }

        // there should be only one.
        for (Property p : node.Instruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(NAT);
            instruction.addInputVariable(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, MAT, ConstraintType.SPLIT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, MAT, ConstraintType.SPLIT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        addVariable(new Term(Rule.createHash(property.toString())).addTypingConstraint(NAT));
        return this;
    }
}
