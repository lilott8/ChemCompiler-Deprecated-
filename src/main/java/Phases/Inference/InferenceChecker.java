package Phases.Inference;

import java.util.Map;
import java.util.Set;

import CompilerDataStructures.ControlFlowGraph.CFG;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InferenceChecker {
    InferenceChecker addCFG(CFG controlFlowGraph);
    InferenceChecker runInference();
    Map<String, Set> getConstraints();
    void addConstraint(String variable, String type);
}
