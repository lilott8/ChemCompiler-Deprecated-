package shared.io.database;

import java.sql.Connection;

import config.ConfigFactory;
import config.DatabaseConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class DatabaseConnector {

    protected DatabaseConfig config = ConfigFactory.getConfig();

    public abstract void closeConnection(Connection connection);

    public abstract Connection getConnection();
}
