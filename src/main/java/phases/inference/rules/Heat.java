package phases.inference.rules;

import java.util.HashSet;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

import static typesystem.epa.ChemTypes.MAT;
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
        logger.info(node);
        logger.debug("InputSymbols: " + node.getInputSymbols());

        for(String s : node.getInputSymbols()) {
            this.addConstraints(s, new HashSet<>(), ConstraintType.HEAT);
        }

        Variable input = new Term(node.getInputSymbols().get(0));
        if (variables.containsKey(input.getVarName())) {
            input.addTypingConstraints(variables.get(input.getVarName()).getTypingConstraints());
        }

        Variable output = input;
        Instruction instruction = new Instruction(node.ID(), Heat.class.getName());
        instruction.addInputTerm(input);
        instruction.addOutputTerm(output);

        addVariable(input);
        addVariable(output);

        for (Property p : node.Instruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addInputTerm(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraints(input, new HashSet<>(), ConstraintType.HEAT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraints(input, new HashSet<>(), ConstraintType.HEAT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        addVariable(new Term(Rule.createHash(property.toString())).addTypingConstraint(REAL));
        this.addConstraint(Rule.createHash(property.toString()), REAL, ConstraintType.NUMBER);
        return this;
    }
}
