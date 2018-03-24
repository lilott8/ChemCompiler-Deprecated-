package shared.variable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

import static ir.Statement.NL;

/**
 * @created: 3/23/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ConstVariable<Value> extends Variable<Value> {

    public static final Logger logger = LogManager.getLogger(ConstVariable.class);

    public ConstVariable(String name) {
        super(name);
    }

    public ConstVariable(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public ConstVariable(String name, Scope scope) {
        super(name, scope);
    }

    public ConstVariable(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type, scope);
    }

    @Override
    public String buildUsage() {
        StringBuilder sb = new StringBuilder();
        //sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"VARIABLE\" : {").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\"").append(NL);
        sb.append("}").append(NL);
        return sb.toString();
    }

    @Override
    public String buildDeclaration() {
        logger.warn("The type for ConstVars should be NUMBER not CHEMICAL");
        StringBuilder sb = new StringBuilder("");

        sb.append("{").append(NL);
        sb.append("\"VARIABLE_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"TYPE\" : \"CHEMICAL\", ").append(NL);
        sb.append(this.addInferredTypes());
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }
}
