package ir.graph;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseStatement implements Statement {

    private static AtomicInteger idCounter = new AtomicInteger(0);

    protected boolean isBranch = false;
    protected boolean fallsThrough = false;
    protected boolean containsInvoke = false;
    protected List<Variable> inputVariables = new ArrayList<>();
    protected List<Variable> properties = new ArrayList<>();
    protected String name;
    protected int id;

    protected BaseStatement(String name) {
        this.name = name;
        this.id = idCounter.getAndIncrement();
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

    @Override
    public int getId() {
        return this.id;
    }

    @Override
    public String getIdAsString() {
        return Integer.toString(this.id);
    }

    @Override
    public void setFallsThrough(boolean fallsThrough) {
        this.fallsThrough = fallsThrough;
    }

    public String toString() {
        return String.format("%s-%d", this.name, this.id);
    }
}
