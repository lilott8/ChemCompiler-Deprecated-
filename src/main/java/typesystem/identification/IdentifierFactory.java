package typesystem.identification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import config.ConfigFactory;
import config.DatabaseConfig;
import config.InferenceConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class IdentifierFactory {

    private static final Identifier identifier;
    private static boolean initialized = false;
    public static final Logger logger = LogManager.getLogger(IdentifierFactory.class);

    static {
        if (ConfigFactory.getConfig().isDBEnabled() && ConfigFactory.getConfig().simulateChemistry()) {
            identifier = new ChemAxonIdentifier();
        } else {
            identifier = new NaiveIdentifier();
        }
    }

    public static Identifier getIdentifier() {
        return identifier;
    }

}
