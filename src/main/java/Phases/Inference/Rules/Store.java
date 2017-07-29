package Phases.Inference.Rules;

import java.util.HashSet;
import java.util.Set;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Callback;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "store")
public class Store implements Callback {

    public Set<String> callback(InstructionNode node) {
        Set<String> results = new HashSet<String>();

        return results;
    }

}
