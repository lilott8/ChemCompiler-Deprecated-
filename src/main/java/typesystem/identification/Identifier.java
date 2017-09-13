package typesystem.identification;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import chemaxon.formats.MolFormatException;
import chemaxon.formats.MolImporter;
import config.ConfigFactory;
import config.InferenceConfig;
import shared.substances.BaseCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Identifier {

    private static final Logger logger = LogManager.getLogger(Identifier.class);
    // This regex should find chemicals...
    private static String formulaRegEx = "[A-Z][a-z]?\\d*|\\((?:[^()]*(?:\\(.*\\))?[^()]*)+\\)\\d+";
    private static String smilesRegEx = "OC[C@@H](O1)[C@@H](O)[C@H](O)[C@@H]2[C@@H]1c3c(O)c(OC)c(O)cc3C(=O)O2";
    private static String inchiKeyRegEx = "/^([0-9A-Z\\-]+)$/";

    protected InferenceConfig config = ConfigFactory.getConfig();

    protected Identifier() {}

    public abstract BaseCompound identifyCompound(String name);
    public abstract BaseCompound identifyCompound(long id);

    /**
     * Test for a CAS number, eg 1354-53-6
     *
     * @param chemical
     * 		String that could be a CAS number
     * @return boolean denoting the input as a CAS or not
     * todo: implement the checksum algorithm for CAS numbers for better handling
     */
    public static boolean isCasNumber(String chemical) {
        logger.fatal("Searching by CAS number is not implemented yet");
        //throw new NotImplementedException();
        try {
            // the first character must be a integer
            Integer.parseInt(chemical.substring(0, 1));
            // as must the last
            Integer.parseInt(chemical.substring(chemical.length() - 1));
            // there must be 2 "-" present
            if (StringUtils.countMatches(chemical, "-") == 2) {
                return true;
            }
        } catch (Exception e) {
            return false;
        }
        return false;
    }

    /**
     * Test for a chemical formula, eg HCl, CH3OOH
     *
     * @param chemical
     * 		String that could be a chemical formula
     * @return boolean denoting the input as a chemical formula or not
     */
    public static boolean isChemicalFormula(String chemical) {
        Pattern pattern = Pattern.compile(formulaRegEx);
        Matcher matcher = pattern.matcher(chemical);

        return matcher.find();
    }

    /**
     * Test to determine whether the string is a smiles
     *
     * @param chemical
     * 		String that could be a SMILES
     * @return boolean denoting the input as a SMILES
     */
    public static boolean isSmiles(String chemical) {
        try {
            MolImporter.importMol(chemical);
            return true;
        } catch (MolFormatException e) {
            return false;
        }
    }

    /**
     * Test for an InChIKey
     *
     * @param chemical
     * 		string that could be a inchikey
     * @return boolean denoting the input as a inchikey or not
     */
    public static boolean isInChIKey(String chemical) {
        Pattern pattern = Pattern.compile(inchiKeyRegEx);
        Matcher matcher = pattern.matcher(chemical);

        return (chemical.length() == 25
                && StringUtils.equals(Character.toString(chemical.charAt(14)), "-")
                && matcher.find());
    }

}
