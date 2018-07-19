package shared.properties;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 7/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Temperature extends Property {

    public Temperature(String name, String units, float value) {
        super(name, units, value);
    }

    public Temperature(String name, String units, float value, Set<ChemTypes> types) {
        super(name, units, value, types);
    }

    @Override
    public String buildDeclaration() {
        return null;
    }

    @Override
    public String buildUsage() {
        String result = "{" + System.lineSeparator();
        result += "\"INPUT_TYPE\":\"PROPERTY\"," + System.lineSeparator();
        result += "\"TEMPERATURE\":" + "{" + System.lineSeparator();
        result += super.getUnitsAndValue() + System.lineSeparator();
        result += "}" + System.lineSeparator();
        result += "}" + System.lineSeparator();
        return result;
    }
}
