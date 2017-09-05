package simulator.database;

import com.zaxxer.hikari.HikariConfig;
import com.zaxxer.hikari.HikariDataSource;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;

import config.Config;
import config.ConfigFactory;
import config.DatabaseConfig;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public enum Hikari implements Connector {
    INSTANCE;

    public static final Logger logger = LogManager.getLogger(Hikari.class);
    private HikariDataSource dataSource;

    Hikari() {
        DatabaseConfig config = ConfigFactory.getConfig();
        HikariConfig hikariConfig = new HikariConfig();
        hikariConfig.setUsername(config.getDBUser());
        hikariConfig.setPassword(config.getDBPassword());
        hikariConfig.setConnectionTimeout(config.getTimeout());
        //hikariConfig.setDataSourceClassName(config.driverClass);
    }


    @Override
    public void closeConnection(Connection connection) {
        try {
            connection.close();
        } catch(SQLException e) {
            logger.error(e.toString());
        }
    }

    @Override
    public Connection getConnection() {
        try {
            return this.dataSource.getConnection();
        } catch(SQLException e) {
            logger.error(e.toString());
        }
        return null;
    }

    public PreparedStatement prepareStatement(String query) throws SQLException {
        return this.dataSource.getConnection().prepareStatement(query);
    }
}
