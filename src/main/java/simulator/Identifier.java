package simulator;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import compilation.datastructures.InstructionNode;
import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.cfg.CFG;
import config.ConfigFactory;
import config.DatabaseConfig;
import simulator.database.Connector;
import simulator.database.Database;
import simulator.database.HikariDB;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Identifier {

    Connector connector;

    public static final Logger logger = LogManager.getLogger(Identifier.class);

    Map<String, Integer> chemToId = new HashMap<>();

    Table<Integer, Integer, Set<Integer>> lookUp = HashBasedTable.create();

    int maxChems = -1;

    public Identifier() {
        DatabaseConfig config = ConfigFactory.getConfig();
        //this.connector = Database.getConnector();

        //maxChems = getMaxChemsFromDB();
        //loadTable();
    }

    public void mapInputsToChemicals(CFG cfg) {
        chemToId.clear();
        int id = 1;
        for (Map.Entry<Integer, BasicBlock> bb : cfg.getBasicBlocks().entrySet()) {
            for(InstructionNode node : bb.getValue().getInstructions()) {
                for (String name : node.getInputSymbols()) {
                    if (!this.chemToId.containsKey(name)) {
                        chemToId.put(name, id);
                        id += 1;
                    }
                }
                for (String name : node.getOutputSymbols()) {
                    if (!this.chemToId.containsKey(name)) {
                        chemToId.put(name, id);
                        logger.info(name, id);
                        id += 1;
                    }
                }
            }
        }
        logger.info(this.chemToId);

        maxChems = id;
    }
    
    private int getMaxChemsFromDB() {
        HikariDB db = HikariDB.INSTANCE;
        Connection connection = this.connector.getConnection();
        PreparedStatement ps = null;
        ResultSet rs = null;
        try {
            rs = db.prepareStatement("SELECT max(rg1) as total FROM reactive_group_combo").executeQuery();
            rs.next();
            return rs.getInt(1);
        } catch (SQLException e) {
            logger.error(e.toString());
        } finally {
            if (rs != null) {try {rs.close();}catch(SQLException ea) {}}
            if (ps != null) {try {ps.close();}catch(SQLException ea) {}}
            this.connector.closeConnection(connection);
        }
        return 0;
    }

    private void loadTable() {
        HikariDB db = HikariDB.INSTANCE;
        Connection connection = this.connector.getConnection();
        PreparedStatement ps = null;
        ResultSet rs = null;
        try {
            rs = db.prepareStatement("SELECT * FROM reactive_group_combo").executeQuery();
            while(rs.next()) {
                int row = rs.getInt(2);
                int column = rs.getInt(3);
                int value = rs.getInt(4);
                if (!this.lookUp.contains(row, column)) {
                    this.lookUp.put(row, column, new HashSet<Integer>());
                }
                this.lookUp.get(row, column).add(value);
            }
        } catch (SQLException e) {
            logger.error(e.toString());
        } finally {
            if (rs != null) {try {rs.close();}catch(SQLException ea) {}}
            if (ps != null) {try {ps.close();}catch(SQLException ea) {}}
            this.connector.closeConnection(connection);
        }
    }
}
