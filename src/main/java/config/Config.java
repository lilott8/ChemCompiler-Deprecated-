package config;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import translators.mfsim.MFSimSSATranslator;
import translators.Translator;
import translators.typesystem.TypeSystemTranslator;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Config implements AlgorithmConfig, TranslateConfig, PhaseConfig, DatabaseConfig, InferenceConfig {

    public static final Logger logger = LogManager.getLogger(Config.class);

    /**
     * Is the compiler in debug mode.
     */
    private boolean debug = false;

    /**
     * List of files to compile
     */
    private List<String> input = new ArrayList<String>();

    /**
     * Where to compile the files to
     */
    private String output = "./";

    /**
     * Run the Single Static Assignment optimization
     */
    private boolean ssa = true;

    /**
     * Run the Single Static Information optimization
     */
    private boolean ssi = false;

    /**
     * Clean the output directory
     */
    private boolean clean = false;

    /**
     * List of translations that need to occur
     */
    private Map<String, Translator> translators = new HashMap<>();

    /**
     * List of phases that are enabled for compilation
     */
    private Set<String> phases = new HashSet<String>();

    /**
     * No default password
     */
    private String dbPassword;
    /**
     * No default username.
     */
    private String dbUser;
    /**
     * Default for address is localhost.
     */
    private String dbAddr = "localhost";
    /**
     * Default for port is 3306.
     */
    private int dbPort = 3306;
    /**
     * Default for timeout is 10 seconds.
     */
    private int dbTimeout = 1000;
    /**
     * Default driver is mariadb jdbc.
     */
    private String dbDriver = "org.mariadb.jdbc.MySQLDataSource";
    /**
     * Default name is empty
     */
    private String dbName = "";
    /**
     * Extra arguments needed to pass to the database.
     */
    private String dbExtras = "";
    /**
     * Simple check to see if we can use the DB or not.
     */
    private final boolean isDBEnabled;

    /**
     * What level the inference engine is supposed to resolve at.
     */
    private InferenceLevel inferenceLevel = InferenceLevel.GENERIC;

    /**
     * Build the config object from our command line
     * This method must match that in the main.
     * @param cmd
     * Command line input
     */
    Config(CommandLine cmd) {
            // get the files for compilation
            this.buildFiles(Arrays.asList(cmd.getOptionValues("compile")));

            // should we run the SSI algorithm
            if (cmd.hasOption("ssi")) {
                this.ssi = true;
            }

            // do we have output
            if (cmd.hasOption("output")) {
                this.output = cmd.getOptionValue("output");
                // Make sure we have the trailing slash.
                if (!StringUtils.equals(this.output.substring(this.output.length()-1), "/")) {
                    this.output += "/";
                }

                // should we clean the output directory
                if (cmd.hasOption("clean")) {
                    this.clean = true;
                    try {
                        FileUtils.cleanDirectory(new File(this.output));
                    } catch (IOException e) {
                        logger.fatal(e);
                    }
                }
            }

            // Are we in debug mode
            this.debug = cmd.hasOption("debug");

            if (cmd.hasOption("translate")) {
                this.buildTranslators(Arrays.asList(cmd.getOptionValues("translate")));
            }

            if (cmd.hasOption("phases")) {
                this.phases.addAll(Arrays.asList(cmd.getOptionValues("phases")));
            }

            // This is technically redundant, this is checked in the main.
            // Build the database config.
            if (cmd.hasOption("dbuser") && cmd.hasOption("dbpass")) {
                this.isDBEnabled = true;
                this.dbUser = cmd.getOptionValue("dbuser");
                this.dbPassword = cmd.getOptionValue("dbpass");
                if (cmd.hasOption("dbport")) {
                    this.dbPort = Integer.parseInt(cmd.getOptionValue("dbport"));
                }
                if (cmd.hasOption("dbaddr")) {
                    this.dbAddr = cmd.getOptionValue("dbaddr");
                }
                if (cmd.hasOption("dbdriver")) {
                    this.dbDriver = cmd.getOptionValue("dbdriver");
                }
                if (cmd.hasOption("dbtimeout")) {
                    this.dbTimeout = Integer.parseInt(cmd.getOptionValue("dbtimeout"));
                }
                if (cmd.hasOption("dbname")) {
                    this.dbName = cmd.getOptionValue("dbname");
                }
                if (cmd.hasOption("dbextras")) {
                    this.dbExtras = cmd.getOptionValue("dbextras");
                }
            } else {
                this.isDBEnabled = false;
            }

            if (cmd.hasOption("resolve")) {
                this.inferenceLevel = InferenceLevel.valueOf(StringUtils.upperCase(cmd.getOptionValue("resolve")));
                if (this.debug) {
                    logger.info("inference level is at: " + this.inferenceLevel);
                }
            }
    }

    /**
     * Part of the InputConfig interface,
     * gets the input files to be compiled.
     *
     * @return      List
     * List of files to compile
     */
    public List<String> getFilesForCompilation() {
        return this.input;
    }

    /**
     * Part of the OutputConfig interface,
     * gets the output file for compilation.
     *
     * @return      String
     * String location for output
     */
    public String getOutputDir() {
        return this.output;
    }

    /**
     * Part of the DebugConfig interface,
     * tells us if we are in testing mode or not.
     * @return  boolean
     * true if we are in testing mode
     */
    public boolean isDebug() {
        return this.debug;
    }

    /**
     * part of the AlgorithmConfig interface,
     * tells us if we should run SSA algorithm
     * @return  boolean
     * true if we should run ssa
     */
    public boolean runSSA() {
        return this.ssa;
    }

    /**
     * Part of the AlgorithmConfig interface,
     * tells us if we should run SSI algorithm
     * @return  boolean
     * true if we should run ssi
     */
    public boolean runSSI() {
        return this.ssi;
    }

    private void buildFiles(List<String> strings) {
        for (String file : strings) {
            File f = new File(file);
            if (f.exists() && !f.isDirectory()) {
                this.input.add(file);
            }
        }
    }

    /**
     * Part of the CleanConfig interface,
     * tells us if we should run the clean method
     * @return boolean
     * true if we should clean the output directory
     */
    public boolean clean() { return this.clean; }

    private void buildTranslators(List<String> strings) {
        for (String name : strings) {
            if (StringUtils.equalsIgnoreCase("mfsim", name)) {
                this.translators.put(TranslateConfig.MFSIM, new MFSimSSATranslator());
            } else if (StringUtils.equalsIgnoreCase("typesystem", name)) {
                this.translators.put(TranslateConfig.TYPESYSTEM, new TypeSystemTranslator());
            }
        }
    }

    /**
     * Part of the TranslateConfig interface,
     * gets all the translations we need to run.
     * @return  Map of translations that can occur
     *     Map of all translations
     */
    public Map<String, Translator> getAllTranslations() {
        return this.translators;
    }

    public boolean translationEnabled(String name) {
        return this.translators.containsKey(name);
    }

    public boolean translationsEnabled() {
        return !this.translators.isEmpty();
    }

    public Set<String> getAllPhases() {
        return this.phases;
    }

    public boolean phasesEnabled() {
        return !this.phases.isEmpty();
    }

    public boolean phaseEnabled(String name) {
        return this.phases.contains(name);
    }


    @Override
    public String getConnectionString() {
        StringBuilder sb = new StringBuilder("jdbc:mysql://");
        sb.append(this.dbAddr).append(":").append(this.dbPort);
        sb.append("/").append(this.dbName);
        if (!StringUtils.isEmpty(this.dbExtras)) {
            sb.append(this.dbExtras);
        }
        return sb.toString();
    }

    @Override
    public String getDBName() {
        return this.dbName;
    }

    @Override
    public String getDBAddr() {
        return this.dbAddr;
    }

    @Override
    public String getDBUser() {
        return this.dbUser;
    }

    @Override
    public int getDBPort() {
        return this.dbPort;
    }

    @Override
    public int getTimeout() {
        return this.dbTimeout;
    }

    @Override
    public String getDBDriver() {
        return this.dbDriver;
    }

    @Override
    public boolean isDBEnabled() {
        return this.isDBEnabled;
    }

    @Override
    public String getDBExtras() {
        return this.dbExtras;
    }

    @Override
    public String getDBPassword() {
        return this.dbPassword;
    }

    @Override
    public InferenceLevel getInferenceLevel() {
        return this.inferenceLevel;
    }
}
