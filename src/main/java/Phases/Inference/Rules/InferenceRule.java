package Phases.Inference.Rules;

import java.util.List;

import CompilerDataStructures.BasicBlock.BasicBlock;
import Phases.Inference.Constraint;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InferenceRule {

    List<Constraint<InferenceTerm>> getConstraints();
    boolean isApplicable(BasicBlock block);
    void parseInstruction(BasicBlock block);

}
