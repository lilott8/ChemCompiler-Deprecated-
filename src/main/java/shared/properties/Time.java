package shared.properties;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 7/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Time extends Property {

    public Time(String name, String units, float value) {
        super(name, units, value);
    }

    public Time(String name, String units, float value, Set<ChemTypes> types) {
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
        result += "\"TIME\": " + "{" + System.lineSeparator();
        result += this.getUnitsAndValue() + System.lineSeparator();
        result += "}" + System.lineSeparator();
        result += "}" + System.lineSeparator();
        return result;
    }
}
