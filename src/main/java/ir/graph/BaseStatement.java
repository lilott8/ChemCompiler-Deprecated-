package ir.graph;

import java.util.ArrayList;
import java.util.List;

import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseStatement implements Statement {

    protected boolean isBranch = false;
    protected boolean fallsThrough = false;
    protected boolean containsInvoke = false;
    protected List<Variable> inputVariables = new ArrayList<>();
    protected List<Variable> properties = new ArrayList<>();
    protected String name;

    public BaseStatement(String name) {
        this.name = name;
    }

    @Override
    public void addInputVariable(Variable variable) {
        this.inputVariables.add(variable);
    }

    @Override
    public List<Variable> getInputVariables() {
        return null;
    }

    @Override
    public List<Variable> getProperties() {
        return this.properties;
    }

    @Override
    public void addProperty(Variable variable) {
        this.properties.add(variable);
    }

    @Override
    public boolean containsInvoke() {
        return this.containsInvoke;
    }

    @Override
    public boolean fallsThrough() {
        return this.fallsThrough;
    }

    @Override
    public boolean isBranch() {
        return this.isBranch;
    }

    @Override
    public String getName() {
        return this.name;
    }

    public String toString() {
        return this.name;
    }
}
