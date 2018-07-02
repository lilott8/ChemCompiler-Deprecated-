package shared.variable;

import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

import static ir.Statement.NL;

/**
 * @created: 3/15/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ManifestVariable<Value> extends Variable<Value> {

    {
        this.isVariable = false;
        this.isGlobal = true;
    }

    public ManifestVariable(String name) {
        super(name);
    }

    public ManifestVariable(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public ManifestVariable(String name, Scope scope) {
        super(name, scope);
    }

    public ManifestVariable(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type, scope);
    }

    @Override
    public String buildDrain() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\":\"VARIABLE\",").append(NL);
        sb.append("\"VARIABLE\":").append("{").append(NL);
        sb.append("\"NAME\":\"").append(this.name).append("\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        return sb.toString();
    }

    @Override
    public String buildHeat() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"VARIABLE\" :").append(NL);
        sb.append("{").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        return sb.toString();
    }

    @Override
    public String buildUsage() {
        StringBuilder sb = new StringBuilder();
        sb.append("{").append(NL);
        sb.append("\"INPUT_TYPE\" : \"VARIABLE\",").append(NL);
        sb.append("\"CHEMICAL\" : {").append(NL);
        sb.append("\"VARIABLE\" : {").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        /* At the beginning*/
        sb.append("\"VOLUME\": ").append("{").append(NL);
        sb.append("\"VALUE\": ").append(this.property.getValue()).append(",").append(NL);
        sb.append("\"UNITS\": \"").append(this.property.getUnits()).append("\"").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        sb.append("}").append(NL);
        return sb.toString();
    }

    @Override
    public String buildDeclaration() {
        StringBuilder sb = new StringBuilder();

        sb.append("{").append(NL);
        sb.append("\"VARIABLE_DECLARATION\" : {").append(NL);
        sb.append("\"ID\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"NAME\" : \"").append(this.name).append("\",").append(NL);
        sb.append("\"TYPE\" : \"CHEMICAL\", ").append(NL);
        sb.append(this.addInferredTypes());
        sb.append("}").append(NL);
        sb.append("}").append(NL);

        return sb.toString();
    }

    @Override
    public String buildVariable() {
        return "";
    }
}
