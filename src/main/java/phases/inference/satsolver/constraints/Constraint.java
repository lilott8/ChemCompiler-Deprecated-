package phases.inference.satsolver.constraints;

import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Constraint {

    enum ConstraintType {
        ASSIGN, MIX, CONST, SPLIT, NUMBER, DETECT, HEAT, OUTPUT, STORE
    }

    void addConstraint(ChemTypes type);
    void addConstraints(Set<ChemTypes> types);
    String buildOutput();
    Set<ChemTypes> getConstraints();
}
