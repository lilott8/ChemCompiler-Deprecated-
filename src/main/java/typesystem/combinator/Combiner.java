package typesystem.combinator;

import org.apache.logging.log4j.LogManager;

import java.util.List;
import java.util.Set;

import config.ConfigFactory;
import shared.substances.BaseCompound;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Combiner {

    BaseCompound combine(BaseCompound a, BaseCompound b);
    Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b);

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
