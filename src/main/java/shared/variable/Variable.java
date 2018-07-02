package shared.variable;

import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import chemical.epa.ChemTypes;
import shared.properties.Property;
import symboltable.Scope;

import static ir.Statement.NL;

/**
 * @created: 2/5/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Variable<Value> implements ScopedVariable, TypedVariable {

    private static AtomicInteger idCounter = new AtomicInteger(0);
    protected String name;
    protected Set<ChemTypes> types = new HashSet<>();
    protected Scope scope;
    protected Value value;
    protected List<Integer> properties = new ArrayList<>();
    protected int id;
    protected boolean isGlobal = false;
    protected boolean isVariable = false;
    protected boolean isConstant = false;
    protected Property property;

    {
        this.id = this.getNewId();
    }

    public Variable(String name) {
        this.name = name;
    }

    public Variable(String name, Set<ChemTypes> type, Property property) {
        this.name = name;
        this.types.addAll(type);
        this.property = property;
    }

    public Variable(String name, Set<ChemTypes> type) {
        this.name = name;
        this.types.addAll(type);
    }

    public Variable(String name, Scope scope) {
        this.name = name;
        this.scope = scope;
    }

    public Variable(String name, Set<ChemTypes> type, Scope scope, Property property) {
        this.name = name;
        this.types.addAll(type);
        this.scope = scope;
        this.property = property;
    }

    public Variable(String name, Set<ChemTypes> type, Scope scope) {
        this.name = name;
        this.types.addAll(type);
        this.scope = scope;
    }


    //abstract public String buildReference();
    abstract public String buildUsage();

    abstract public String buildDeclaration();

    public abstract String buildVariable();

    public Property getProperty() {
        return this.property;
    }

    public void setProperty(Property property) {
        this.property = property;
    }

    private int getNewId() {
        return idCounter.getAndIncrement();
    }

    public String getVarName() {
        return this.name;
    }

    public Variable addTypingConstraints(Set<ChemTypes> constraints) {
        this.types.addAll(constraints);
        return this;
    }

    public Variable addTypingConstraint(ChemTypes constraint) {
        this.types.add(constraint);
        return this;
    }

    public Value getValue() {
        return this.value;
    }

    public Variable setValue(Value value) {
        this.value = value;
        return this;
    }

    public boolean isConstant() {
        return this.isConstant;
    }

    public boolean isGlobal() {
        return this.isGlobal;
    }

    public void addScope(Scope scope) {
        this.scope = scope;
    }

    public Scope getScope() {
        return this.scope;
    }

    public String getName() {
        return this.name;
    }

    public String getScopedName() {
        return this.scope.getName() + "_" + this.name;
    }

    public Set<ChemTypes> getTypes() {
        return this.types;
    }

    public Set<ChemTypes> getTypingConstraints() {
        return this.types;
    }

    public boolean isVariable() {
        return isVariable;
    }

    public String toString() {
        String ret = this.name + "\t" + this.types;
        if (this.scope != null) {
            ret += "\t Scope Name: " + this.scope.getName();
        }
        return ret;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }

        Variable other = (Variable) obj;

        return StringUtils.equals(other.name, this.name) && this.types.equals(other.types);
    }

    public String addInferredTypes() {
        StringBuilder sb = new StringBuilder();
        if (!this.types.isEmpty()) {
            sb.append("\"INFERRED TYPES\" : [").append(NL);
            int x = 0;
            for (ChemTypes t : this.types) {
                sb.append(t.getValue());
                if (x < this.types.size() - 1) {
                    sb.append(", ");
                }
                x++;
            }
            sb.append(NL);
            sb.append("]").append(NL);
        } else {
            sb.append(NL);
        }
        return sb.toString();
    }

    public String buildInput() {
        StringBuilder sb = new StringBuilder();
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"CHEMICAL\" : {").append(NL);
        sb.append("\"VARIABLE\" : {").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\"").append(NL);
        sb.append("}").append(NL);
        if (!this.properties.isEmpty()) {

        }
        sb.append("}").append(NL);
        return sb.toString();
    }

    public String buildReference() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\", ").append(NL);
        sb.append("\"VARIABLE\" : ").append(NL);
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }

    public String redeclare() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(NL);
        sb.append("\"VARIABLE_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"TYPE\" : \"VARIABLE\", ").append(NL);
        sb.append(this.addInferredTypes());
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        return sb.toString();
    }
}
