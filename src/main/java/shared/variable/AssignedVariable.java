package shared.variable;

import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

import static ir.statements.Statement.NL;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class AssignedVariable<Value> extends Variable<Value> {

    public AssignedVariable(String name) {
        super(name);
    }

    public AssignedVariable(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public AssignedVariable(String name, Scope scope) {
        super(name, scope);
    }

    public AssignedVariable(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type, scope);
    }

    @Override
    public String buildDeclaration() {
        StringBuilder sb = new StringBuilder("");

        sb.append("\"VARIABLE_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"TYPE\" : \"CHEMICAL\", ").append(NL);
        sb.append(this.addInferredTypes());
        sb.append("}").append(NL);

        return sb.toString();
    }
}
