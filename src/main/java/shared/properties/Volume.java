package shared.properties;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 7/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Volume extends Property {

    public Volume(String name, String units, float value) {
        super(name, units, value);
    }

    public Volume(String name, String units, float value, Set<ChemTypes> types) {
        super(name, units, value, types);
    }

    @Override
    public String buildDeclaration() {
        return null;
    }

    @Override
    public String buildUsage() {
        String result = "\"VOLUME\": " + "{" + System.lineSeparator();
        result += this.getUnitsAndValue() + System.lineSeparator();
        result += "}" + System.lineSeparator();
        return result;
    }
}
