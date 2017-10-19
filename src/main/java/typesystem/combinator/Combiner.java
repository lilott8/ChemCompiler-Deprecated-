package typesystem.combinator;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import config.ConfigFactory;
import shared.substances.BaseCompound;
import shared.substances.NaiveCompound;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Combiner {

    Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b);

    default BaseCompound combine(BaseCompound a, BaseCompound b) {
        BaseCompound compound = new NaiveCompound(-1);
        compound.addReactiveGroup(a.getReactiveGroups());
        compound.addReactiveGroup(b.getReactiveGroups());

        List<ChemTypes> listA = new ArrayList<>();
        List<ChemTypes> listB = new ArrayList<>();

        listA.addAll(a.getReactiveGroups());
        listB.addAll(b.getReactiveGroups());

        this.combine(a, b);

        return compound;
    }

    default boolean combine(ChemTypes a, ChemTypes b) {
        if (ConfigFactory.getConfig().isDebug()) {
            return EpaManager.INSTANCE.test(a, b);
        } else {
            return EpaManager.INSTANCE.validate(a, b);
        }
    }

    default boolean combine(List<ChemTypes> a, List<ChemTypes> b) {
        for (int x = 0; x < a.size(); x++) {
            for (int y = 0; y < b.size(); y++) {
                if (ConfigFactory.getConfig().isDebug()) {
                    EpaManager.INSTANCE.test(a.get(x), b.get(y));
                } else {
                    EpaManager.INSTANCE.validate(a.get(x), b.get(y));
                }
            }
        }
        return true;
    }

    default boolean combine(List<ChemTypes> types) {
        for (int x = 0; x < types.size(); x++) {
            for (int y = x; y < types.size(); y++) {
                if (ConfigFactory.getConfig().isDebug()) {
                    EpaManager.INSTANCE.test(types.get(x), types.get(y));
                } else {
                    EpaManager.INSTANCE.validate(types.get(x), types.get(y));
                }
            }
        }
        return true;
    }
}
