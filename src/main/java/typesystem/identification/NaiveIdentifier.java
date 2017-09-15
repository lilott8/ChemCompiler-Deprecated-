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
        return new HashSet<>();
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(long id) {
        return new HashSet<>();
    }
}
