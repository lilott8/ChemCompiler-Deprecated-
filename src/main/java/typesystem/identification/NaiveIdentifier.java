package typesystem.identification;

import shared.substances.BaseCompound;
import shared.substances.NaiveCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveIdentifier extends Identifier {

    NaiveIdentifier() {}

    @Override
    public BaseCompound identifyCompound(String name) {
        return new NaiveCompound(-1, name);
    }

    @Override
    public BaseCompound identifyCompound(long id) {
        return new NaiveCompound(id);
    }
}
