package ir.statements;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import chemical.epa.ChemTypes;
import shared.variable.Property;
import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseStatement implements Statement {

    private static AtomicInteger idCounter = new AtomicInteger(0);

    protected boolean isBranch = false;
    protected boolean isAssign = false;
    protected boolean fallsThrough = false;
    protected boolean containsInvoke = false;
    protected Variable outputVariable;
    protected List<Variable> inputVariables = new ArrayList<>();
    protected Map<String, Variable> properties = new HashMap<>();
    protected Set<ChemTypes> types = new HashSet<>();
    protected String name;
    protected int id;

    protected BaseStatement(String name) {
        this.name = name;
        this.id = idCounter.getAndIncrement();
    }

    public void generateNewId() {
        this.id = idCounter.getAndIncrement();
    }

    @Override
    public Set<ChemTypes> getType() {
        return this.types;
    }


    @Override
    public void addInputVariable(Variable variable) {
        this.inputVariables.add(variable);
        this.types.addAll((Set<ChemTypes>) variable.getTypes());
    }

    @Override
    public List<Variable> getInputVariables() {
        return this.inputVariables;
    }

    @Override
    public void addOutputVariable(Variable variable) {
        this.outputVariable = variable;
    }

    public Variable getOutputVariable() {
        return outputVariable;
    }

    @Override
    public Map<String, Variable> getProperties() {
        return this.properties;
    }

    @Override
    public void addProperty(String name, Variable variable) {
        this.properties.put(name, variable);
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

    public String print(String indent) {
        String name;
        if (!this.isAssign && !this.isBranch) {
            if (this.inputVariables.isEmpty()) {
                name = this.outputVariable.getName();
            } else {
                name = this.inputVariables.get(0).getName();
            }
        } else {
            if (isAssign) {
                name = "assign";
            } else {
                name = "branch";
            }
        }
        return String.format("%s%s%s-%d (Input: %s)", indent, "\t", this.name, this.id, name);
    }

    protected String propertyToJson(String property) {
        StringBuilder sb = new StringBuilder();
        if (this.properties.containsKey(Property.TIME)) {
            Property time = (Property) this.properties.get(Property.TIME);
            // The Temp
            sb.append(",{").append(NL);
            sb.append("\"INPUT_TYPE\" : \"PROPERTY\",").append(NL);
            sb.append("\"TIME\" : ");
            // Temp object.
            sb.append("{").append(NL);
            sb.append("\"VALUE\" : ").append(time.getValue()).append(", ").append(NL);
            sb.append("\"UNITS\" : ").append("\"").append(time.getUnits()).append("\"").append(NL);
            sb.append("}").append(NL);
            sb.append("}").append(NL);
        }
        return sb.toString();
    }
}
