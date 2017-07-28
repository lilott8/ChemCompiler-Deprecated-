package Phases.Inference.Rules;

import org.apache.logging.log4j.LogManager;

import java.util.Set;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Callback;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "mix")
public class Mix implements Callback {

    public Set<String> callback(InstructionNode node) {
        LogManager.getLogger(Mix.class).warn("Here");
        return null;
    }
}
