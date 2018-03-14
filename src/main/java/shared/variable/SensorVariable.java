package shared.variable;

import java.util.Set;

import ir.Statement;
import symboltable.Scope;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SensorVariable<Value> extends Variable<Value> {

    public SensorVariable(String name) {
        super(name);
    }

    public SensorVariable(String name, Set type) {
        super(name, type);
    }

    public SensorVariable(String name, Scope scope) {
        super(name, scope);
    }

    public SensorVariable(String name, Set type, Scope scope) {
        super(name, type, scope);
    }

    @Override
    public String buildDeclaration() {
        StringBuilder sb = new StringBuilder();

        sb.append("\"SENSOR_DECLARATION\" : {").append(Statement.NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(Statement.NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(Statement.NL);
        sb.append("\"TYPE\" : \"SENSOR\", ").append(Statement.NL);
        sb.append(this.addInferredTypes());
        sb.append("}").append(Statement.NL);

        return sb.toString();
    }
}
