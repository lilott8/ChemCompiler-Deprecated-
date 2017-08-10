package Phases.Inference.Rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference;
import substance.Property;

/**
 * @created: 8/10/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "combine", ruleType = "instruction")
public class Combine extends Rule {

    public static final Logger logger = LogManager.getLogger(Mix.class);

    public Combine(Inference.InferenceType type) {
        super(type);
    }

    public Rule gatherConstraints(InstructionNode node) {

        for (String out : node.get_def()) {
            this.addConstraint(out, "Mat");
        }

        for (String in : node.get_use()) {
            this.addConstraint(in, "Mat");
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.addConstraint("constant", "Real");
        }
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, MAT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, MAT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(CONST, REAL);
        return this;
    }
}
