package Phases.Inference.Rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * Mat = mix Mat with Mat ... for Real
 */
@InferenceRule(ruleName = "mix", ruleType = "instruction")
public class Mix extends Rule {

    public static final Logger logger = LogManager.getLogger(Mix.class);

    public Mix(InferenceType type) {
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
