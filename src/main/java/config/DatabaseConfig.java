package config;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface DatabaseConfig extends CommonConfig {

    String getConnectionString();
    String getDBName();
    String getDBAddr();
    String getDBPassword();
    String getDBUser();
    int getDBPort();
    int getTimeout();
    String getDBDriver();
    boolean isDBEnabled();
    String getDBExtras();
}
