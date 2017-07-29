package Phases.Inference.Rules;

import java.util.HashSet;
import java.util.Set;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Callback;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "nat")
public class Nat implements Callback {

    public Set<String> callback(InstructionNode node) {
        Set<String> results = new HashSet<String>();

        return results;
    }
}
