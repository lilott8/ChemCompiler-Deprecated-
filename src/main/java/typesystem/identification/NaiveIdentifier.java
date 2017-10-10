package typesystem.identification;

import java.util.HashSet;
import java.util.Set;

import shared.substances.BaseCompound;
import shared.substances.NaiveCompound;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveIdentifier extends Identifier {

    NaiveIdentifier() {}

    @Override
    public NaiveCompound identifyCompound(String name) {
        return new NaiveCompound(-1, name);
    }

    @Override
    public NaiveCompound identifyCompound(long id) {
        return new NaiveCompound(id);
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(String name) {
        Set<ChemTypes> types = new HashSet<>();
        int total = 0;
        for (Character c : name.toCharArray()) {
            total += c;
        }
        types.add(ChemTypes.getTypeFromId(total%ChemTypes.NUM_REACTIVE_GROUPS));
        return types;
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(long id) {
        Set<ChemTypes> types = new HashSet<>();
        types.add(ChemTypes.getTypeFromId(((int) id%ChemTypes.NUM_REACTIVE_GROUPS)));
        return types;
    }
}
