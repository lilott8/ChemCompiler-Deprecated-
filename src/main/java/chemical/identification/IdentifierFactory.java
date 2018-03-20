package chemical.identification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import config.Config;
import config.ConfigFactory;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class IdentifierFactory {

    public static final Logger logger = LogManager.getLogger(IdentifierFactory.class);
    private static final Identifier identifier;
    private static final Config config = ConfigFactory.getConfig();

    static {
        String message = "";
        if (config.isDBEnabled() && config.simulateChemistry()) {
            message = "Using ChemAxon identifier.";
            identifier = new ChemAxonIdentifier();
        } else if (config.isDBEnabled()) {
            message = "Using Inference identifier.";
            identifier = new InferenceIdentifier();
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
