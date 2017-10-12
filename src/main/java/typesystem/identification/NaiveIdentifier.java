package typesystem.identification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

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

    public static final Logger logger = LogManager.getLogger(NaiveIdentifier.class);

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
        logger.debug("==============");
        logger.debug(total%ChemTypes.NUM_REACTIVE_GROUPS);
        int modulus = total%ChemTypes.NUM_REACTIVE_GROUPS;
        if (modulus == 0 || modulus == 67) {
            modulus = 1;
        }

        types.add(ChemTypes.getTypeFromId(modulus));
        logger.debug(types);
        logger.debug("==============");
        return types;
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(long id) {
        Set<ChemTypes> types = new HashSet<>();
        types.add(ChemTypes.getTypeFromId(((int) id%ChemTypes.NUM_REACTIVE_GROUPS)));
        return types;
    }
}
