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

    private Set<Integer> unknowns = new HashSet<Integer>(){{
        unknowns.add(0);
        unknowns.add(67);
        unknowns.add(24);
        unknowns.add(36);
        unknowns.add(43);
    }};

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
        types.add(ChemTypes.getTypeFromId(this.getModulo(total)));
        return types;
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(long id) {
        Set<ChemTypes> types = new HashSet<>();
        types.add(ChemTypes.getTypeFromId((this.getModulo(id))));
        return types;
    }

    private int getModulo(long x) {
        int modulus = (int) x%ChemTypes.NUM_REACTIVE_GROUPS;

        if (unknowns.contains(modulus)) {
            modulus = 1;
        }
        return modulus;
    }
}
