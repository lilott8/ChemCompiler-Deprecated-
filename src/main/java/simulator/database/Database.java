package simulator.database;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Database {

    public static Connector getConnector() {
        // TODO: build logic to handle multiple engines.
        return Hikari.INSTANCE;
    }
}
