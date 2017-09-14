package typesystem.identification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import chemaxon.formats.MolFormatException;
import chemaxon.formats.MolImporter;
import io.Connector;
import io.ConnectorFactory;
import io.DatabaseConnector;
import shared.substances.BaseCompound;
import shared.substances.ChemAxonCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemAxonIdentifier extends Identifier {
    public static final Logger logger = LogManager.getLogger(ChemAxonIdentifier.class);

    ChemAxonIdentifier() {}

    /**
     * Use the io.database to classify a compound.  This takes in a string, is
     *
     * @param name
     * 		string representation of the name, the system will determine whether the string is a CAS-Number, SMILES,
     * 		InChiKey, or name.
     * @return a compound object from the io.database
     */
    public BaseCompound identifyCompound3(String name) {
        ChemAxonCompound compound = null;
        logger.warn("Using smiles for the where clause.");
        String where = Representation.getColumn(Representation.SMILES);
        String query = String.format("SELECT DISTINCT(c.pubchem_id), crg.reactive_groups_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id WHERE %s = ?", where);
        DatabaseConnector database = ConnectorFactory.getConnection();
        Connection connection = database.getConnection();
        try {
            PreparedStatement statement = connection.prepareStatement(query);
            statement.setString(1, name);
            ResultSet rs = statement.executeQuery();
            int reactiveGroup;
            while (rs.next()) {
                if (compound == null) {
                    compound = new ChemAxonCompound(rs.getLong("pubchem_id"), name);
                }
                reactiveGroup = rs.getInt("reactive_groups_id");
                if (reactiveGroup > 0) {
                    compound.addReactiveGroup(reactiveGroup);
                }
            }
            if (compound != null) {
                try {
                    compound.setMolecule(MolImporter.importMol(name));
                } catch (MolFormatException e) {
                    logger.error(name + " has an error in the smiles and could not be imported into chemaxon");
                }
            }
            // Close the result set.
            rs.close();
        } catch (SQLException e) {
            logger.warn(e.toString());
        }
        database.closeConnection(connection);
        return compound;
    }

    public BaseCompound identifyCompound(String name) {
        ChemAxonCompound compound = null;
        boolean done = false;
            switch(config.getClassificationLevel()) {
                // pubchem
                case 16:
                    try {
                        int x = Integer.parseInt(name);
                        compound = this.searchByPubChemId(x);
                        break;
                    } catch(NumberFormatException e) {}
                // cas-number
                case 8:
                    if (isCasNumber(name)) {
                        compound = this.searchByCasNumber(name);
                        if (compound != null) {
                            break;
                        }
                    }
                // inchl-key
                case 4:
                    if (isInChIKey(name)) {
                        compound = this.searchByInCHLKey(name);
                        if (compound != null) {
                            break;
                        }
                    }
                // smiles
                case 2:
                    if (isSmiles(name)) {
                        compound = this.searchBySmiles(name);
                        if (compound != null) {
                            break;
                        }
                    }
                default:
                // naive name approach
                case 1:
                    compound = this.searchByAliases(name);
                    break;
        }
        return compound;
    }

    public BaseCompound identifyCompound(long pubchem) {
        ChemAxonCompound compound = null;
        String where = Representation.getColumn(Representation.PUBCHEM_ID);
        String query = String.format("SELECT c.pubchem_id, c.canonical_smiles, rg.epa_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id " +
                "LEFT JOIN reactive_groups rg on crg.reactive_groups_id = rg.id WHERE c.%s = ?", where);
        DatabaseConnector database = ConnectorFactory.getConnection();
        Connection connection = database.getConnection();
        try {
            PreparedStatement statement = connection.prepareStatement(query);
            statement.setLong(1, pubchem);
            ResultSet rs = statement.executeQuery();
            int reactiveGroup;
            while (rs.next()) {
                if (compound == null) {
                    compound = new ChemAxonCompound(pubchem, rs.getString("canonical_smiles"));
                }
                reactiveGroup = rs.getInt("epa_id");
                if (reactiveGroup > 0) {
                    compound.addReactiveGroup(reactiveGroup);
                }
            }
            if (compound != null) {
                try {
                    compound.setMolecule(MolImporter.importMol(compound.getName()));
                } catch (MolFormatException e) {
                    logger.error(pubchem + " has an error in the smiles and could not be imported into chemaxon");
                }
            }
            // Close the result set!
            rs.close();
        } catch (SQLException e) {
            logger.warn(e.toString());
        }
        database.closeConnection(connection);
        return compound;
    }

    /**
     * set the identification method for this run
     * @param s
     * @return
     */
    public Identifier identify(String s) {
        if (Identifier.isSmiles(s)) {
            //this.representation = Representation.SMILES;
        } else if (Identifier.isInChIKey(s)) {
           // this.representation = Representation.INCHIKEY;
        } else if (Identifier.isCasNumber(s)) {
            logger.fatal("Cas numbers cannot be used yet");
           // throw new NotImplementedException();
        } else if (Identifier.isChemicalFormula(s)) {
           // this.representation = Representation.FORMULA;
        } else {
           // this.representation = Representation.NAME;
        }
        return this;
    }

    private ChemAxonCompound searchByPubChemId(int id) {
        return null;
    }

    private ChemAxonCompound searchByCasNumber(String number) {
        return null;
    }

    private ChemAxonCompound searchByInCHLKey(String key) {
        return null;
    }

    private ChemAxonCompound searchBySmiles(String smiles) {
        return null;
    }

    private ChemAxonCompound searchByAliases(String name) {
        return null;
    }

}
