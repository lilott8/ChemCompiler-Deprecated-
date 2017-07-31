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

        // logger.debug("Id: " + node.ID());
        // logger.debug("Input Symbols: " + node.getInputSymbols());
        // logger.debug("Properties: " + node.Instruction().getProperties());
        // logger.debug("Use: " + node.get_use());
        // logger.debug("Def: " + node.get_def());
        // logger.debug("Output Symbols: " + node.getOutputSymbols());
        // logger.debug("toString(): " + node.toString());

        return this;
    }
}
