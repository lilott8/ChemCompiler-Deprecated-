package Config;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import Translators.MFSimSSA.MFSimSSATranslator;
import Translators.Translator;
import Translators.TypeSystem.TypeSystemTranslator;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public enum Config implements DebugConfig, InputConfig, OutputConfig, AlgorithmConfig, TranslateConfig {
    INSTANCE;

    public static final Logger logger = LogManager.getLogger(Config.class);

    /**
     * Local variable used to guarantee we only build once
     */
    private boolean built = false;

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
     * List of translations that need to occur
     */
    private Map<String, Translator> translators = new HashMap<String, Translator>();

    /**
     * Build the config object from our command line
     * This method must match that in the main.
     * @param cmd
     * Command line input
     */
    public void buildConfig(CommandLine cmd) {
        if(!this.built) {
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
            }

            // Are we in debug mode
            this.debug = Boolean.parseBoolean(cmd.getOptionValue("debug", "false"));

            if (cmd.hasOption("translate")) {
                this.buildTranslators(Arrays.asList(cmd.getOptionValues("translate")));
            }

            this.built = true;
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
    public String getOuptutDir() {
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


    private void buildTranslators(List<String> strings) {
        for (String name : strings) {
            if (StringUtils.equalsIgnoreCase("mfsim", name)) {
                this.translators.put("mfsim", new MFSimSSATranslator());
            }
            else if (StringUtils.equalsIgnoreCase("typesystem", name)) {
                this.translators.put("typesystem", new TypeSystemTranslator());
            }
        }
    }

    private void buildFiles(List<String> strings) {
        for (String file : strings) {
            File f = new File(file);
            if (f.exists() && !f.isDirectory()) {
                this.input.add(file);
            }
        }
    }

    public Translator getTranslationByName(String name) {
        if (this.translators.containsKey(name)) {
            return this.translators.get(name);
        }
        return null;
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


}
