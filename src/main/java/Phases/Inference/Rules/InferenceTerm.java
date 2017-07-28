package Phases.Inference.Rules;

import Phases.Inference.Constraint;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InferenceTerm extends InferenceRule {

    Constraint<String> getTermTyping();

}
