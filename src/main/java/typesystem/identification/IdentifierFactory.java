package typesystem.identification;

import config.ConfigFactory;
import config.DatabaseConfig;
import config.InferenceConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class IdentifierFactory {

    private static InferenceConfig config = ConfigFactory.getConfig();
    private static DatabaseConfig dbConfig = ConfigFactory.getConfig();
    private static final Identifier identifier;

    static {
        if (dbConfig.isDBEnabled() && config.simulateChemistry()) {
            identifier = new ChemAxonIdentifier();
        } else {
            identifier = new NaiveIdentifier();
        }
    }

    public static Identifier getIdentifier() {
        return identifier;
    }

}
