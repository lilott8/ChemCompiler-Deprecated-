package typesystem.identification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Set;

import chemaxon.formats.MolFormatException;
import chemaxon.formats.MolImporter;
import io.Connector;
import io.ConnectorFactory;
import io.DatabaseConnector;
import shared.substances.BaseCompound;
import shared.substances.ChemAxonCompound;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemAxonIdentifier extends Identifier {
    public static final Logger logger = LogManager.getLogger(ChemAxonIdentifier.class);

    ChemAxonIdentifier() {}

    public ChemAxonCompound identifyCompound(String name) {
        ChemAxonCompound compound;
            switch(config.getClassificationLevel()) {
                // pubchem
                case 16:
                    try {
                        long x = Long.parseLong(name);
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

    @Override
    public BaseCompound identifyCompound(long id) {
        return this.searchByPubChemId(id);
    }

    @Override
    public Set<ChemTypes> identifyCompoundForTypes(String name) {
        return this.identifyCompound(name).getReactiveGroups();
    }

    public Set<ChemTypes> identifyCompoundForTypes(long id) {
        return this.searchByPubChemId(id).getReactiveGroups();
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

    private ChemAxonCompound searchByPubChemId(long id) {
        ChemAxonCompound compound = null;
        String where = Representation.getColumn(Representation.PUBCHEM_ID);
        String query = String.format("SELECT c.pubchem_id, c.canonical_smiles, rg.epa_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id " +
                "LEFT JOIN reactive_groups rg on crg.reactive_groups_id = rg.id WHERE c.%s = ?", where);
        DatabaseConnector database = ConnectorFactory.getConnection();
        Connection connection = database.getConnection();
        try {
            PreparedStatement statement = connection.prepareStatement(query);
            statement.setLong(1, id);
            ResultSet rs = statement.executeQuery();
            int reactiveGroup;
            while (rs.next()) {
                if (compound == null) {
                    compound = new ChemAxonCompound(id, rs.getString("canonical_smiles"));
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
                    logger.error(id + " has an error in the smiles and could not be imported into chemaxon");
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

    private ChemAxonCompound searchByCasNumber(String number) {
        return null;
    }

    private ChemAxonCompound searchByInCHLKey(String key) {
        return null;
    }

    private ChemAxonCompound searchBySmiles(String smiles) {
        ChemAxonCompound compound = null;
        logger.warn("Using smiles for the where clause.");
        String where = Representation.getColumn(Representation.SMILES);
        String query = String.format("SELECT DISTINCT(c.pubchem_id), crg.reactive_groups_id FROM chemicals c " +
                "LEFT JOIN chemicals_reactive_groups crg ON c.pubchem_id = crg.pubchem_id WHERE %s = ?", where);
        DatabaseConnector database = ConnectorFactory.getConnection();
        Connection connection = database.getConnection();
        try {
            PreparedStatement statement = connection.prepareStatement(query);
            statement.setString(1, smiles);
            ResultSet rs = statement.executeQuery();
            int reactiveGroup;
            while (rs.next()) {
                if (compound == null) {
                    compound = new ChemAxonCompound(rs.getLong("pubchem_id"), smiles);
                }
                reactiveGroup = rs.getInt("reactive_groups_id");
                if (reactiveGroup > 0) {
                    compound.addReactiveGroup(reactiveGroup);
                }
            }
            if (compound != null) {
                try {
                    compound.setMolecule(MolImporter.importMol(smiles));
                } catch (MolFormatException e) {
                    logger.error(smiles + " has an error in the smiles and could not be imported into chemaxon");
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

    private ChemAxonCompound searchByAliases(String name) {
        return null;
    }

}
