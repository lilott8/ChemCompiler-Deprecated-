package ir;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import chemical.epa.ChemTypes;
import shared.variable.Method;
import shared.properties.Property;
import shared.variable.Variable;
import symboltable.SymbolTable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseStatement implements Statement {

    public static final Logger logger = LogManager.getLogger(BaseStatement.class);
    private static AtomicInteger idCounter = new AtomicInteger(0);
    protected boolean isBranch = false;
    protected boolean isAssign = false;
    protected boolean fallsThrough = false;
    protected boolean containsInvoke = false;
    protected List<Variable> outputVariables = new ArrayList<>();
    protected List<Variable> inputVariables = new ArrayList<>();
    protected Map<String, Property> properties = new HashMap<>();
    protected Set<ChemTypes> types = new HashSet<>();
    protected String name;
    protected String methodName = SymbolTable.DEFAULT_SCOPE;
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

    public void addInputVariables(List<Variable> variables) {
        for (Variable v : variables) {
            this.addInputVariable(v);
        }
    }

    public String getMethodName() {
        return methodName;
    }

    public void setMethodName(String methodName) {
        this.methodName = methodName;
    }

    public void clearInputVariables() {
        this.inputVariables.clear();
    }

    @Override
    public List<Variable> getInputVariables() {
        return this.inputVariables;
    }

    @Override
    public void addOutputVariable(Variable variable) {
        this.outputVariables.add(variable);
    }

    public List<Variable> getOutputVariables() {
        return outputVariables;
    }

    @Override
    public Map<String, Property> getProperties() {
        return this.properties;
    }

    @Override
    public void addProperty(String name, Property variable) {
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
                name = this.outputVariables.get(0).getName();
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
            Property time = this.properties.get(Property.TIME);
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

    public void alphaConversion(List<Variable> params) {
        Method method = SymbolTable.INSTANCE.getMethods().get(this.methodName);
        // The list of new variables to be used.
        List<Variable> variables = new ArrayList<>();
        // Branch statements need to be handled differently
        // Easy way to iterate the statements input variables.
        for (int x = 0; x < this.inputVariables.size(); x++) {
            // We know that if it is in the parameters, then we need to replace it.
            if (method.getParameters().containsKey(this.inputVariables.get(x).getName())) {
                int counter = 0;
                for (Variable getIndex : method.getIndexedParameters()) {
                    if (StringUtils.equalsIgnoreCase(getIndex.getName(), this.inputVariables.get(x).getName())) {
                        variables.add(params.get(counter));
                    }
                    counter++;
                }
            }
        }
        this.inputVariables.clear();
        this.inputVariables.addAll(variables);
    }
}
