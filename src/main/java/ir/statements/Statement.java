package ir.statements;

import java.util.List;

import shared.variable.Variable;
import typesystem.satsolver.constraints.SMTSolver;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Statement extends Vertex, SMTSolver {

    List<Variable> getInputVariables();
    List<Variable> getProperties();
    void addInputVariable(Variable variable);
    void addProperty(Variable variable);

    void setFallsThrough(boolean fallsThrough);

    boolean containsInvoke();

    boolean fallsThrough();
    boolean isBranch();
}
