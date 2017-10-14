package phases.inference.rules;

import com.sun.tools.javac.tree.DCTree;

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
@InferenceRule(ruleName = "detect", ruleType = "term")
public class Detect extends NodeAnalyzer {

    public Detect(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {

        for (String input : node.getInputSymbols()) {
            // this.addConstraints(input, new HashSet<>(), ConstraintType.DETECT);
        }

        for (String output : node.getOutputSymbols()) {
            this.addConstraint(output, REAL, ConstraintType.NUMBER);
        }
        Variable input = variables.get(node.getInputSymbols().get(0));
        if (input == null) {
            logger.warn("input is null!?");
        }

        Variable output = new Term(node.getOutputSymbols().get(0));
        output.addTypingConstraint(REAL);

        Instruction instruction = new Instruction(node.ID(), Detect.class.getName());
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
        this.addConstraints(input, new HashSet<>(), ConstraintType.DETECT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, REAL, ConstraintType.NUMBER);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(Rule.createHash(property.toString()), REAL, ConstraintType.NUMBER);
        return this;
    }
}
