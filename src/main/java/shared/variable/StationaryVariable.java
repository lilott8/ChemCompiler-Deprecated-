package shared.variable;

import java.util.Set;

import chemical.epa.ChemTypes;
import ir.statements.Statement;
import symboltable.Scope;

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

        sb.append("\"VARIABLE_DECLARATION\" : {").append(Statement.NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(Statement.NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(Statement.NL);
        sb.append("\"TYPE\" : \"STATIONARY\", ");
        sb.append(this.addInferredTypes());
        sb.append("}").append(Statement.NL);

        return sb.toString();
    }
}
