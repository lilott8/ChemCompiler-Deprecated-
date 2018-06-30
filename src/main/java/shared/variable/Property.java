package shared.variable;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 3/13/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Property {

    public static final String TIME = "TIME";
    public static final String VOLUME = "VOLUME";
    public static final String TEMP = "TEMP";
    public static final String QUANTITY = "QUANTITY";
    public static final String CONDITIONAL = "CONDITIONAL";

    private String name;
    private String units;
    private float value;
    private Set<ChemTypes> types = new HashSet<>();
    private String opType;

    public Property(String name, String opType, String units, float value) {
        this.name = name;
        this.units = units;
        this.value = value;
        this.opType = opType;
        this.types.add(ChemTypes.NAT);
        this.types.add(ChemTypes.REAL);
    }

    public Property(String name, String opType, String units, float value, Set<ChemTypes> types) {
        this.name = name;
        this.units = units;
        this.value = value;
        this.opType = opType;
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

    public String getOpType() {
        return opType;
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

    public String buildDeclaration() {
        return null;
    }

    public String buildUsage() {
        StringBuilder sb = new StringBuilder();
        return sb.toString();
    }
}
