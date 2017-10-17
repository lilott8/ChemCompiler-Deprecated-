package typesystem.identification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import config.Config;
import config.ConfigFactory;
import config.DatabaseConfig;
import config.InferenceConfig;
import phases.PhaseFacade;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class IdentifierFactory {

    private static final Identifier identifier;
    private static final Config config = ConfigFactory.getConfig();
    public static final Logger logger = LogManager.getLogger(IdentifierFactory.class);

    static {
        String message = "";
        if (config.isDBEnabled() && config.phaseEnabled(PhaseFacade.PHASES.INFERENCE)) {
            message = "Using Inference identifier.";
            identifier = new InferenceIdentifier();
        } else if (config.isDBEnabled() && config.simulateChemistry()) {
            message = "Using ChemAxon identifier.";
            identifier = new ChemAxonIdentifier();
        } else {
            message = "Using naive classifier.";
            identifier = new NaiveIdentifier();
        }

        if (ConfigFactory.getConfig().isDebug()) {
            logger.info(message);
        }
    }

    public static Identifier getIdentifier() {
        return identifier;
    }

}
