package shared.properties;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 3/13/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Property {

    public static final String TIME = "TIME";
    public static final String VOLUME = "VOLUME";
    public static final String TEMP = "TEMP";
    public static final String QUANTITY = "QUANTITY";
    public static final String CONDITIONAL = "CONDITIONAL";

    protected String name;
    protected String units;
    protected float value;
    protected Set<ChemTypes> types = new HashSet<>();

    public Property(String name, String units, float value) {
        this.name = name;
        this.units = units;
        this.value = value;
        this.types.add(ChemTypes.NAT);
        this.types.add(ChemTypes.REAL);
    }

    public Property(String name, String units, float value, Set<ChemTypes> types) {
        this.name = name;
        this.units = units;
        this.value = value;
        this.types.addAll(types);
    }

    public String getName() {
        return name;
    }

    public float getValue() {
        return value;
    }

    public Set<ChemTypes> getTypes() {
        return types;
    }

    public void addTypingConstraint(ChemTypes type) {
        this.types.add(type);
    }

    public void addTypingConstraints(Set<ChemTypes> types) {
        this.types.addAll(types);
    }

    public String getUnits() {
        return units;
    }

    public void setUnits(String units) {
        this.units = units;
    }

    public abstract String buildDeclaration();

    public abstract String buildUsage();

    protected String getUnitsAndValue() {
        String result = "\"VALUE\":" + this.value + "," + System.lineSeparator();
        result += "\"UNITS\": \"" + this.units + "\"" + System.lineSeparator();
        return result;
    }
}
