package io.database;

import com.zaxxer.hikari.HikariConfig;
import com.zaxxer.hikari.HikariDataSource;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class HikariDB extends DatabaseConnector {

    private HikariDataSource dataSource;

    private static final Logger logger = LogManager.getLogger(HikariDB.class);

    HikariDB() {
        HikariConfig hikariConfig = new HikariConfig();
        hikariConfig.setJdbcUrl(config.getConnectionString());
        hikariConfig.setUsername(config.getDBUser());
        hikariConfig.setPassword(config.getDBPassword());
        hikariConfig.setConnectionTimeout(config.getTimeout());
        //hikariConfig.setDataSourceClassName(config.driverClass);
        // Ensure we have large enough pool size relative to the max threads.
        this.dataSource = new HikariDataSource(hikariConfig);
    }

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

    @Override
    public void closeConnection(Connection connection) {
        try {
            connection.close();
        } catch(SQLException e) {
            logger.error(e.toString());
        }
    }

}
