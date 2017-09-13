package typesystem.identification;

import java.util.Set;

import phases.inference.ChemTypes;
import shared.substances.BaseCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveIdentifier extends Identifier {

    @Override
    public BaseCompound identifyCompound(String name) {
        return null;
    }

    @Override
    public BaseCompound identifyCompound(long id) {
        return null;
    }
}
