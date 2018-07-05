package ir;

import java.util.List;
import java.util.Map;
import java.util.Set;

import chemical.epa.ChemTypes;
import shared.properties.Property;
import shared.variable.Variable;
import typesystem.satsolver.constraints.SMTSolver;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Statement extends Vertex, SMTSolver, Exportable, Convertable {

    String NL = System.lineSeparator();

    List<Variable> getInputVariables();

    List<Variable> getOutputVariables();

    Map<String, Property> getProperties();

    String getMethodName();

    void setMethodName(String name);

    void addInputVariable(Variable variable);

    void addInputVariables(List<Variable> variables);

    void clearInputVariables();

    void addOutputVariable(Variable variable);

    void addProperty(String name, Property variable);

    Set<ChemTypes> getType();

    void setFallsThrough(boolean fallsThrough);

    boolean containsInvoke();

    boolean fallsThrough();

    boolean isBranch();

    String print(String indent);
}
