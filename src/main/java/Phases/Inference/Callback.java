package Phases.Inference;

import java.util.Map;
import java.util.Set;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference.InferenceType;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Callback {

    Map<String, Set<String>> callback(InstructionNode node);
    Callback setType(InferenceType type);
    InferenceType getType();

    default void addConstraint() {

    }
}
