package io;

import org.apache.commons.lang3.StringUtils;

import java.util.HashMap;
import java.util.Map;

import config.ConfigFactory;
import config.DatabaseConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ConnectorFactory {

    private static DatabaseConfig config = ConfigFactory.getConfig();
    private static DatabaseConnector connection;
    public static final String DEFAULT = "mysql";
    public static final String MYSQL = "mysql";
    public static final String HIKARI = "hikari";
    private static String CURRENT = "";

    static {
        if (config.isDBEnabled()) {
            if (StringUtils.containsIgnoreCase(config.getDBDriver(), HIKARI)) {
                connection = new HikariDB();
                CURRENT = HIKARI;
            } else {
                connection = new MySQLDB();
                CURRENT = MYSQL;
            }
        }
    }

    private ConnectorFactory() {}

    /**
     * Build a connection to a io.database
     *
     * @return connector to io.database
     */
    public static DatabaseConnector getConnection() {
        return connection;
    }
}
