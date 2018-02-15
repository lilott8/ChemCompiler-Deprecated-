package shared;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Variable {
    String getVarName();
    Set<ChemTypes> getTypingConstraints();
    Variable addTypingConstraints(Set<ChemTypes> constraints);
    Variable addTypingConstraint(ChemTypes constraint);
}
