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
import java.util.List;
import java.util.Map;

import shared.ReportingLevel;
import translators.Translator;
import translators.mfsim.MFSimSSATranslator;
import translators.typesystem.TypeSystemTranslator;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Config implements AlgorithmConfig, TranslateConfig, DatabaseConfig, InferenceConfig {

    public static final Logger logger = LogManager.getLogger(Config.class);

    private static String TS_LEVEL_ERROR = "ERROR";
    private static String TS_LEVEL_WARN = "WARN";
    private static String TS_LEVEL_NONE = "NONE";

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
    private boolean isDBEnabled = false;
    /**
     * What scope is the classification engine allowed to run at?
     */
    private int classificationLevel = 2;
    /**
     * Level of error reporting in the typesystem
     */
    private ReportingLevel errorLevel = ReportingLevel.ERROR;
    /**
     * Are we ignoring warnings?
     */
    private boolean ignoreWarnings = false;
    /**
     * Does the EPAManager build the filters or not?
     */
    private boolean buildFilters = true;
    /**
     * Where is the location of the epa defs.
     */
    private String epaDefs = "src/main/resources/epa.xml";
    /**
     * Where is the location of the reactive matrix.
     */
    private String reactiveMatrix = "src/main/resources/abstract-interpretation.txt";
    /**
     * Use 3rd party chemistry software to simulate mixes.
     */
    private boolean simulateChemistry = false;
    /**
     * Minimum length of the SMARTS notation to use as a filter.
     */
    private int smartsSize = -1;
    /**
     * Number of threads to be used.
     */
    private int maxThreads = 1;
    /**
     * Should the compiler pay attention to the def/use chain And throw an error if a resource is
     * attempted to be used in a mix/split after it's been used already.
     */
    private boolean monitorResources = true;
    /**
     * Should the system verify that ChemAxon is installed.
     * DEFAULT: true
     */
    private boolean checkForChemAxon = true;

    /**
     * Build the config object from our command line This method must match that in the main.
     *
     * @param cmd Command line input
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
            if (!StringUtils.equals(this.output.substring(this.output.length() - 1), "/")) {
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

        this.monitorResources = !cmd.hasOption("drm");

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
        }

        if (cmd.hasOption("classify")) {
            int level = Integer.parseInt(cmd.getOptionValue("classify"));
            // handles the case that we have the minimum level.
            level = (level <= 0) ? 1 : level;
            // Handles the case where we input a number > 16.
            level = (level > 16) ? 16 : level;
            // We can save the level!
            this.classificationLevel = (int) Math.pow(2, (Integer.SIZE - Integer.numberOfLeadingZeros(level)) - 1);
        }

        if (cmd.hasOption("threads")) {
            this.maxThreads = Integer.parseInt(cmd.getOptionValue("threads"));
            this.maxThreads = this.maxThreads < 1 ? 1 : this.maxThreads;
        }

        if (cmd.hasOption("smarts")) {
            this.smartsSize = Integer.parseInt(cmd.getOptionValue("smarts"));
            this.smartsSize = this.smartsSize < 1 ? 1 : this.smartsSize;
        }

        if (cmd.hasOption("typesystem")) {
            String level = cmd.getOptionValue("typesystem");
            if (StringUtils.equalsIgnoreCase(TS_LEVEL_NONE, level)) {
                logger.error("System is running with no type checking!");
                this.errorLevel = ReportingLevel.NONE;
            } else if (StringUtils.equalsIgnoreCase(TS_LEVEL_WARN, level)) {
                logger.error("System will only validate errors.");
                this.errorLevel = ReportingLevel.WARNING;
            } else {
                this.errorLevel = ReportingLevel.ERROR;
            }
        }

        // Default is build them, so if we don't have it, we build the filters.
        this.buildFilters = !cmd.hasOption("nofilters");

        this.simulateChemistry = cmd.hasOption("simulate");

        if (cmd.hasOption("epadefs")) {
            this.epaDefs = cmd.getOptionValue("epadefs");
        }

        if (cmd.hasOption("matrix")) {
            this.reactiveMatrix = cmd.getOptionValue("matrix");
        }

        if (cmd.hasOption("nochemaxon")) {
            this.checkForChemAxon = false;
        }
    }

    /**
     * Part of the InputConfig interface, gets the input files to be compiled.
     *
     * @return List List of files to compile
     */
    public List<String> getFilesForCompilation() {
        return this.input;
    }

    /**
     * Part of the OutputConfig interface, gets the output file for compilation.
     *
     * @return String String location for output
     */
    public String getOutputDir() {
        return this.output;
    }

    /**
     * Part of the DebugConfig interface, tells us if we are in testing mode or not.
     *
     * @return boolean true if we are in testing mode
     */
    public boolean isDebug() {
        return this.debug;
    }

    /**
     * part of the AlgorithmConfig interface, tells us if we should run SSA algorithm
     *
     * @return boolean true if we should run ssa
     */
    public boolean runSSA() {
        return this.ssa;
    }

    /**
     * Part of the AlgorithmConfig interface, tells us if we should run SSI algorithm
     *
     * @return boolean true if we should run ssi
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
     * Part of the CleanConfig interface, tells us if we should run the clean method
     *
     * @return boolean true if we should clean the output directory
     */
    public boolean clean() {
        return this.clean;
    }

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
     * Part of the TranslateConfig interface, gets all the translations we need to run.
     *
     * @return Map of translations that can occur Map of all translations
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
    public int getClassificationLevel() {
        return this.classificationLevel;
    }

    @Override
    public boolean buildFilters() {
        return this.buildFilters;
    }

    @Override
    public String getEpaDefs() {
        return this.epaDefs;
    }

    @Override
    public String getReactiveMatrix() {
        return this.reactiveMatrix;
    }

    @Override
    public boolean simulateChemistry() {
        return this.simulateChemistry;
    }

    @Override
    public int smartsLength() {
        return this.smartsSize;
    }

    @Override
    public int getNumberOfThreads() {
        return this.maxThreads;
    }

    @Override
    public boolean monitorResources() {
        return this.monitorResources;
    }

    @Override
    public boolean checkForChemAxon() {
        return this.checkForChemAxon;
    }

    @Override
    public ReportingLevel getErrorLevel() {
        return this.errorLevel;
    }
}
