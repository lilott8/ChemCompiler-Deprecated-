package shared.io.database;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import config.ConfigFactory;
import config.DatabaseConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MySQLDB extends DatabaseConnector {

    public static final Logger logger = LogManager.getLogger(MySQLDB.class);
    protected java.sql.Connection connection;
    protected Statement statement;
    protected DatabaseConfig config = ConfigFactory.getConfig();
    protected String lastQuery;

    protected MySQLDB() {
        try {
            String url = String.format("jdbc:mysql://%s/%s?" +
                            "useJDBCCompliantTimezoneShift=true&useLegacyDatetimeCode=false&serverTimezone=UTC",
                    config.getDBAddr(), config.getDBName());
            if (config.isDebug()) {
                logger.debug(url);
            }
            connection = DriverManager.getConnection(url, config.getDBUser(), config.getDBPassword());
        } catch (Exception e) {
            logger.fatal(e.toString());
        }
    }

    public Connection getConnection() {
        return this.connection;
    }

    /**
     * Allows updating of record
     *
     * @param query string that is an update
     *
     * @return number of records affected
     */
    public int update(String query) {
        try {
            this.statement = this.connection.createStatement();
            if (this.config.isDebug()) {
                logger.debug(query);
            }
            this.lastQuery = query;
            return this.statement.executeUpdate(query);
        } catch (SQLException e) {
            logger.error(e.toString());
            return -1;
        }
    }

    /**
     * General query to the shared.io.database
     *
     * @param query string that is a query
     *
     * @return ResultSet object that is the results of your query
     */
    public ResultSet query(String query) {
        try {
            this.statement = this.connection.createStatement();
            if (this.config.isDebug()) {
                logger.debug(query);
            }
            this.lastQuery = query;
            return this.statement.executeQuery(query);
        } catch (SQLException e) {
            logger.error(e.toString());
            return null;
        }
    }

    /**
     * Get a prepared statement for the query you want to run
     *
     * @param query prepared statement form of a query
     *
     * @return prepared statement for use in querying shared.io.database
     *
     * @throws SQLException ...
     */
    public PreparedStatement prepareStatement(String query) throws SQLException {
        return this.connection.prepareStatement(query);
    }

    public void closeConnection(Connection connection) {
        try {
            connection.close();
        } catch (SQLException e) {
            logger.error(e.toString());
        }
    }
}
