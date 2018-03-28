package shared.variable;

import java.util.Set;

import chemical.epa.ChemTypes;
import symboltable.Scope;

/**
 * @created: 3/13/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Property<Value> extends Variable<Value> {

    public static final String TIME = "TIME";
    public static final String VOLUME = "VOLUME";
    public static final String TEMP = "TEMP";
    public static final String QUANTITY = "QUANTITY";

    String units;

    public Property(String name) {
        super(name);
    }

    public Property(String name, Set<ChemTypes> type) {
        super(name, type);
    }

    public Property(String name, Scope scope) {
        super(name, scope);
    }

    public Property(String name, Set<ChemTypes> type, Scope scope) {
        super(name, type, scope);
    }

    public String getUnits() {
        return units;
    }

    public void setUnits(String units) {
        this.units = units;
    }

    @Override
    public String buildDeclaration() {
        return null;
    }

    @Override
    public String buildUsage() {
        StringBuilder sb = new StringBuilder("");
        return sb.toString();
    }
}
