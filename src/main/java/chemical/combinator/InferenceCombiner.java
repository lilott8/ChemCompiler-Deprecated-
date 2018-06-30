package chemical.combinator;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import chemical.epa.EpaManager;
import config.ConfigFactory;

/**
 * @created: 10/17/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InferenceCombiner implements Combiner {

    public static final Logger logger = LogManager.getLogger(InferenceCombiner.class);

    @Override
    public Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b) {
        logger.warn(a);
        logger.warn(b);
        Set<ChemTypes> chemTypes = new HashSet<>();

        for (ChemTypes t1 : a) {
            for (ChemTypes t2 : b) {
                if (ConfigFactory.getConfig().isDebug()) {
                    chemTypes.addAll(EpaManager.INSTANCE.lookUp(t1, t2));
                    if (!EpaManager.INSTANCE.test(t1, t2) && ConfigFactory.getConfig().isDebug()) {
                        logger.debug(t1 + " + " + t2 + " generates: " + EpaManager.INSTANCE.getReaction(t1, t2));
                    }
                } else {
                    if (EpaManager.INSTANCE.validate(t1, t2)) {
                        chemTypes.addAll(EpaManager.INSTANCE.lookUp(t1, t2));
                    }
                }
            }
        }

        return chemTypes;
    }
}
