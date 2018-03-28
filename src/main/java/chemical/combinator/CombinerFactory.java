package chemical.combinator;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import config.Config;
import config.ConfigFactory;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CombinerFactory {

    public static final Logger logger = LogManager.getLogger(CombinerFactory.class);
    private static final Combiner combiner;
    private static Config config = ConfigFactory.getConfig();

    static {
        String message = "";
        if (config.simulateChemistry()) {
            message = "Using ChemAxon combiner.";
            combiner = new ChemAxonCombiner();
        } else {
            message = "Using Inference combiner.";
            combiner = new InferenceCombiner();
        }

        if (config.isDebug()) {
            logger.info(message);
        }
    }

    public static Combiner getCombiner() {
        return combiner;
    }

}
