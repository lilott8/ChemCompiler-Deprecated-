package simulator.database;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Connector {
    void closeConnection(Connection connection);
    Connection getConnection();
    PreparedStatement prepareStatement(String query) throws SQLException;
}
