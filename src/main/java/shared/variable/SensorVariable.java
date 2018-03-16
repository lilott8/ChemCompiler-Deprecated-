package shared.variable;

import java.util.Set;

import static ir.Statement.NL;
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

        sb.append("{").append(NL);
        sb.append("\"SENSOR_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"TYPE\" : \"SENSOR\", ").append(NL);
        sb.append(this.addInferredTypes());
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }

    @Override
    public String buildUsage() {
        return null;
    }
}
