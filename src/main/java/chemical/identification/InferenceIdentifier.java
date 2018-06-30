package chemical.identification;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import config.Config;
import config.ConfigFactory;
import shared.io.database.ConnectorFactory;
import shared.io.database.DatabaseConnector;
import shared.substances.BaseCompound;
import shared.substances.NaiveCompound;

/**
 * @created: 10/17/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InferenceIdentifier extends Identifier {

    public static final Logger logger = LogManager.getLogger(InferenceIdentifier.class);
    Config config = ConfigFactory.getConfig();

    @Override
    public BaseCompound identifyCompound(String name) {
        return new NaiveCompound(-1, name);
    }

    @Override
    public BaseCompound identifyCompound(long id) {
        return new NaiveCompound(id);
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(String name) {
        Set<ChemTypes> results = new HashSet<>();
        switch (config.getClassificationLevel()) {
            // pubchem
            // With this case, if we can run, it is authoritative.
            // Such that, if this runs, whatever is returned is
            // the absolute best we can do.
            case 16:
                try {
                    long x = Long.parseLong(name);
                    results = this.searchByPubChemId(x);
                    break;
                } catch (NumberFormatException e) {
                }
                // Cas-No: Here, we have to use the tuple return.
            case 8:
                if (isCasNumber(name)) {
                    results.addAll(this.searchByCasNumber(name));
                    break;
                }
                // inchl-key
            case 4:
                if (isInChIKey(name)) {
                    results.addAll(this.searchByInCHLKey(name));
                    break;
                }
                // smiles
            case 2:
                if (isSmiles(name)) {
                    results.addAll(this.searchBySmiles(name));
                    break;
                }
            default:
                // naive name approach
            case 1:
                results.addAll(this.searchByAliases("%" + name + "%"));
                break;
        }
        return results;
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(long id) {
        return this.searchByPubChemId(id);
    }

    private Set<ChemTypes> searchByInCHLKey(String inchi) {
        String query = String.format("SELECT DISTINCT(c.pubchem_id), rg.epa_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id " +
                "LEFT JOIN reactive_groups rg on crg.reactive_groups_id = rg.`id` " +
                "WHERE %s = ?", Representation.getColumn(Representation.INCHIKEY));
        return this.issueQuery(query, inchi, "epa_id");
    }

    private Set<ChemTypes> searchBySmiles(String smiles) {
        String query = String.format("SELECT DISTINCT(c.pubchem_id), rg.epa_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id " +
                "LEFT JOIN reactive_groups rg on crg.reactive_groups_id = rg.`id` " +
                "WHERE %s = ?", Representation.getColumn(Representation.SMILES));
        return this.issueQuery(query, smiles, "epa_id");
    }

    private Set<ChemTypes> searchByAliases(String name) {
        String query = String.format("SELECT DISTINCT(c.pubchem_id), rg.epa_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id " +
                "LEFT JOIN reactive_groups rg on crg.reactive_groups_id = rg.`id` " +
                "WHERE c.%s LIKE ?", Representation.getColumn(Representation.NAME));
        return this.issueQuery(query, name, "epa_id");
    }

    private Set<ChemTypes> searchByCasNumber(String cas) {
        logger.fatal("Searching by CAS number is not implemented yet");
        return this.issueQuery("", cas, "");
    }

    private Set<ChemTypes> searchByPubChemId(long id) {
        String query = String.format("SELECT rg.epa_id FROM chemicals c " +
                        "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id " +
                        "LEFT JOIN reactive_groups rg on crg.reactive_groups_id = rg.id WHERE c.%s = ?",
                Representation.getColumn(Representation.PUBCHEM_ID));
        return this.issueQuery(query, id, "epa_id");
    }

    private Set<ChemTypes> issueQuery(String query, long parameter, String column) {
        Set<ChemTypes> results = new HashSet<>();
        DatabaseConnector database = ConnectorFactory.getConnection();
        Connection connection = database.getConnection();
        try {
            PreparedStatement statement = connection.prepareStatement(query);
            statement.setLong(1, parameter);
            ResultSet rs = statement.executeQuery();
            int reactiveGroup;
            while (rs.next()) {
                reactiveGroup = rs.getInt(column);
                if (reactiveGroup > 0) {
                    results.add(ChemTypes.getTypeFromId(reactiveGroup));
                }
            }
            // Close the result set.
            rs.close();
        } catch (SQLException e) {
            logger.error(e.toString());
            logger.info("Long: " + query);
            results.add(ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
        }
        // database.closeConnection(connection);
        return results;
    }

    /**
     * Search by string-based field.
     */
    private Set<ChemTypes> issueQuery(String query, String parameter, String column) {
        if (StringUtils.contains(parameter, "_")) {
            parameter = StringUtils.replaceAll(parameter, "_", " ");
        }
        Set<ChemTypes> results = new HashSet<>();
        DatabaseConnector database = ConnectorFactory.getConnection();
        Connection connection = database.getConnection();
        try {
            PreparedStatement statement = connection.prepareStatement(query);
            statement.setString(1, parameter);
            ResultSet rs = statement.executeQuery();
            int reactiveGroup;
            while (rs.next()) {
                reactiveGroup = rs.getInt(column);
                if (reactiveGroup > 0) {
                    results.add(ChemTypes.getTypeFromId(reactiveGroup));
                }
            }
            // Close the result set.
            rs.close();
            if (results.isEmpty()) {
                results.add(ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
            }
        } catch (SQLException e) {
            logger.error(e.toString());
            logger.info("String: " + query);
            results.add(ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
        }
        // database.closeConnection(connection);
        logger.info(parameter + ": " + results);
        return results;
    }
}
