package Phases.Inference.Rules;

import org.apache.logging.log4j.LogManager;

import java.util.HashSet;
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
        Set<String> results = new HashSet<String>();
        LogManager.getLogger(Mix.class).warn(node.getInputSymbols());
        LogManager.getLogger(Mix.class).warn(node.get_use());

        return results;
    }
}
