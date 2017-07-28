package Phases.Inference;

import java.util.Set;

import CompilerDataStructures.InstructionNode;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Callback {

    Set<String> callback(InstructionNode node);
}
