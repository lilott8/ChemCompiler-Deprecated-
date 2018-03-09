package ir.graph;

import java.util.List;

import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Statement extends Vertex {

    List<Variable> getInputVariables();
    List<Variable> getProperties();
    void addInputVariable(Variable variable);
    void addProperty(Variable variable);

    void setFallsThrough(boolean fallsThrough);

    boolean containsInvoke();

    boolean fallsThrough();
    boolean isBranch();
}
