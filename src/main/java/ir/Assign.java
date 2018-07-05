package ir;

import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Assign extends Statement {

    void setLeftOp(Variable variable);

    void setRightOp(Statement statement);

    List<Variable> getOutputVariables();

    Set<ChemTypes> getTypes();
}
