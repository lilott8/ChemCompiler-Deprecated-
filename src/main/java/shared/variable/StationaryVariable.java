package shared.variable;

import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

import static ir.Statement.NL;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class StationaryVariable<Value> extends Variable<Value> {

    public StationaryVariable(String name) {
        super(name);
    }

    public StationaryVariable(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public StationaryVariable(String name, Scope scope) {
        super(name, scope);
    }

    public StationaryVariable(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type, scope);
    }

    @Override
    public String buildDeclaration() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(NL);
        sb.append("\"VARIABLE_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"TYPE\" : \"STATIONARY\", ");
        sb.append(this.addInferredTypes());
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }

    public String buildUsage() {
        StringBuilder sb = new StringBuilder();

        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"STATIONARY\" : {").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\"").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }
}
