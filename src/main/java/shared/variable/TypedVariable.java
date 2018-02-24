package shared.variable;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 2/23/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface TypedVariable {
    TypedVariable addTypingConstraints(Set<ChemTypes> constraints);
    TypedVariable addTypingConstraint(ChemTypes constraint);
    Set<ChemTypes> getTypes();
}
