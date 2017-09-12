package phases.inference;

import java.util.Set;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Constraint {

    void addConstraint(ChemTypes type);
    void addConstraints(Set<ChemTypes> types);
    String buildOutput();
    Set<ChemTypes> getConstraints();
}
