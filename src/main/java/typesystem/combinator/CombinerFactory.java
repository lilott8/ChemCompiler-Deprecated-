package typesystem.combinator;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import config.Config;
import config.ConfigFactory;
import config.InferenceConfig;
import phases.PhaseFacade;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CombinerFactory {

    private static Config config = ConfigFactory.getConfig();
    private static final Combiner combiner;
    public static final Logger logger = LogManager.getLogger(CombinerFactory.class);

    static {
        String message = "";
        if (config.phaseEnabled(PhaseFacade.PHASES.INFERENCE)) {
            message = "Using inference combiner.";
            combiner = new InferenceCombiner();
        } else if (config.simulateChemistry()) {
            message = "Using ChemAxon combiner.";
            combiner = new ChemAxonCombiner();
        } else {
            message = "Using naive combiner.";
            combiner = new NaiveCombiner();
        }

        if (config.isDebug()) {
            logger.info(message);
        }
    }

    public static Combiner getCombiner() {
        return combiner;
    }

}
