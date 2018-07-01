package shared.properties;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 7/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Quantity extends Property {
    public Quantity(String name, String units, float value) {
        super(name, units, value);
    }

    public Quantity(String name, String units, float value, Set<ChemTypes> types) {
        super(name, units, value, types);
    }

    @Override
    public String buildDeclaration() {
        return null;
    }

    @Override
    public String buildUsage() {
        String result = "{" + System.lineSeparator();
        result += "\"INPUT_TYPE\": \"PROPERTY\"," + System.lineSeparator();
        result += "\"PROPERTY\":" + "{" + System.lineSeparator();
        result += "\"TYPE\": \"SPLIT_NUM\", " + System.lineSeparator();
        result += this.getUnitsAndValue() + System.lineSeparator();
        result += "}" + System.lineSeparator();
        result += "}" + System.lineSeparator();
        return result;
    }
}
