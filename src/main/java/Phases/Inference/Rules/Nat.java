package Phases.Inference.Rules;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Callback;
import Phases.Inference.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "nat", ruleType = "term")
public class Nat extends Rule {

    public Nat(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherConstraints(InstructionNode node) {
        return null;
    }
}
