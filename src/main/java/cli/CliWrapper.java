package cli;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.lang.StringUtils;
import org.apache.commons.lang.SystemUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;

import config.Config;
import config.ConfigFactory;
import shared.errors.ConfigurationException;

/**
 * @created: 9/14/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CliWrapper {
    public static final Logger logger = LogManager.getLogger(CliWrapper.class);
    private CommandLine cmd;
    private CommandLineParser parser = new DefaultParser();
    private boolean addOptionals = false;

    public CliWrapper() {
    }

    private static boolean checkForChemAxon() {
        String licensePath = "";
        String userName = System.getProperty("user.name");
        if (SystemUtils.IS_OS_WINDOWS) {
            licensePath += String.format("C:\\Users\\%s\\chemaxon\\license.cxl", userName);
        } else {
            licensePath += String.format("/Users/%s/.chemaxon/license.cxl", userName);
        }

        if (!new File(licensePath).exists()) {
            logger.fatal("ChemAxon license file not found. Please view: https://docs.chemaxon.com/display/docs/Installing+licenses+LIC");
            logger.fatal("Please use the '-nca' flag to acknowledge you want to run BioScript without ChemAxon.");
            throw new ConfigurationException("Chem Axon License file not found.");
        }
        return true;
    }

    public void parseCommandLine(String... args) {
        try {
            this.cmd = this.parser.parse(this.buildOptions(), args);
            this.initializeEnvironment(this.cmd);
        } catch (ParseException e) {
            logger.fatal("Error parsing command line, illegal command: " + Arrays.toString(args));
            logger.fatal(e);
        }
    }

    private void initializeEnvironment(final CommandLine cmd) {
        // see if we asked for help...
        if (cmd.hasOption("help")) {
            HelpFormatter hf = new HelpFormatter();
            hf.printHelp("BioScript", buildOptions(), true);
            System.exit(0);
        }

        // See if we have the argument we need.
        if (!cmd.hasOption("compile")) {
            throw new ConfigurationException("No input file to compile given.");
        }

        // If we have a translator we must also have output.
        if ((cmd.hasOption("translate") && !cmd.hasOption("output"))) {
            throw new ConfigurationException("If you provide a translation or an output, the other must accompany.");
        }

        if ((cmd.hasOption("clean") && !cmd.hasOption("output"))) {
            throw new ConfigurationException("Attempting to clean output directory, but no directory supplied.");
        }

        if (!validateDatabase(cmd)) {
            throw new ConfigurationException("We cannot infer the connection data for the database.");
        }

        // initialize our config object.
        Config config = ConfigFactory.buildConfig(cmd);

        // add any initializing statements derived from the command line here.
        if (StringUtils.isEmpty(config.getInputFile())) {
            throw new ConfigurationException("We have no valid file(s) for input");
        }

        if (config.checkForChemAxon()) {
            checkForChemAxon();
        }
    }

    /**
     * Builds the command line options needed to run the program
     */
    private Options buildOptions() {
        Options options = new Options();

        // File(s) to compile
        String desc = "Compile the source file(s)\n" +
                "Usage: -c /path/to/file_to_compile.json";
        options.addOption(Option.builder("c").longOpt("compile")
                .desc(desc).hasArgs().required().numberOfArgs(1).type(String.class)
                .argName("compile").required(true).build());

        // Testing mode
        desc = "Debug mode\n" +
                "Usage: -d";
        options.addOption(Option.builder("d").longOpt("debug")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("debug").build());



        // Output file option
        desc = "Place output in which directory.  If -t is set, this must be set." +
                "\n Usage: -o /path/to/output/";
        options.addOption(Option.builder("o").longOpt("output")
                .desc(desc).type(String.class).hasArg().required(true)
                .argName("output").build());

        // What translators to use
        desc = "What translator to use.  If -o is set, this must be set.\n" +
                "Usage: -translate {list of translators}\n" +
                "Available translators: \n" +
                "\tmfsim: translates cfg to mfsim machine code";
        options.addOption(Option.builder("t").longOpt("translate")
                .desc(desc).type(ArrayList.class).hasArgs().required(false)
                .argName("translate").build());
        // Clean output option
        desc = "Clean the output directory. If -clean is set, -o (output) must be set." +
                "\nUsage: -clean";
        options.addOption(Option.builder("clean").longOpt("clean")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("clean").build());
        // classification scope
        desc = "What level to attempt to classify materials at: \n" +
                "\t0\t=>\tDisable identification\n" +
                "\t1\t=>\tNaive, string-based approach\n" +
                "\t2\t=>\tSMILES notation (Default)\n" +
                "\t4\t=>\tInCHL-Key\n" +
                "\t8\t=>\tCAS-Number\n" +
                "\t16\t=>\tPubChemId\n" +
                "\nUsage: -classify [0|1|2|4|8|16]";
        options.addOption(Option.builder("classify").longOpt("classify")
                .desc(desc).type(Integer.class).hasArg().required(false)
                .argName("classify").build());
        // Simulate using ChemAxon
        desc = "Simulate chemistry using a computational chemical library.\n" +
                "This is disabled by default.\n" +
                "Usage: -s";
        options.addOption(Option.builder("s").longOpt("simulate")
                .desc(desc).hasArg(false).required(false)
                .argName("simulate").build());
        // Enforcement level
        desc = "What level to report type system shared.errors.\n" +
                "Usage: -ts {error|warn|none}";
        options.addOption(Option.builder("ts").longOpt("typesystem")
                .desc(desc).type(String.class).hasArg(true).required(false)
                .argName("ts").build());
        // Build the filters
        desc = "Disable building the SMART filters.  This is only disabled for testing purposes.\n" +
                "Usage: -nf";
        options.addOption(Option.builder("nf").longOpt("nofilters")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("nofilters").build());
        // Definitions of EPA reactive groups
        desc = "Path for EPA config file.  Defaults to internally installed file.\n" +
                "Usage: -epadefs [/path/to/file.xml]";
        options.addOption(Option.builder("epadefs").longOpt("epadefs")
                .desc(desc).type(String.class).hasArg().required(true)
                .argName("epadefs").build());
        // Minimum char limit for smart filters.
        desc = "Minimum size of SMARTS filter to use.  Default is maximum.\n" +
                "Usage: -smarts [number of chars]\n";
        options.addOption(Option.builder("smarts").longOpt("smarts")
                .desc(desc).type(Integer.class).hasArg().required(false)
                .argName("smarts").build());
        // Ignore chemical usage monitoring
        desc = "Disable resource monitoring, i.e. ignore a mix using " +
                "the same chemical.\n" +
                "Usage: -drm";
        options.addOption(Option.builder("drm").longOpt("drm")
                .desc(desc).type(String.class).required(false)
                .argName("drm").build());
        // Database name
        desc = "Database name.\n" +
                "Usage: -dbname [name]";
        options.addOption(Option.builder("dbname").longOpt("dbname")
                .desc(desc).hasArg().argName("dbname").build());
        // Database user name
        desc = "Database user name.\n" +
                "Usage -dbuser [name]";
        options.addOption(Option.builder("dbuser").longOpt("dbuser")
                .desc(desc).hasArg().argName("dbuser").build());
        // Database password
        desc = "Database password.\n" +
                "Usage -dbpass [pass]";
        options.addOption(Option.builder("dbpass").longOpt("dbpass")
                .desc(desc).hasArg().argName("dbpass").build());
        // Database port
        desc = "Database port, default: 3306.\n" +
                "Usage -dbport [port]";
        options.addOption(Option.builder("dbport").longOpt("dbport")
                .desc(desc).hasArg().argName("dbport").build());
        // Database address
        desc = "Database address, default localhost.\n" +
                "Usage -dbaddr [addr]";
        options.addOption(Option.builder("dbaddr").longOpt("dbaddr")
                .desc(desc).hasArg().argName("dbaddr").build());
        // Database driver, e.g. org.mariadb.jdbc.MySQLDataSource
        desc = "Database driver default mysql. Can be multiple, seperate by comma (,).\n" +
                "Usage: -dbdriver [mysql|hikari]";
        options.addOption(Option.builder("dbdriver").longOpt("dbdriver")
                .desc(desc).hasArg().argName("dbdriver").build());
        // Database timeout
        desc = "Database timeout, default 10 seconds.\n" +
                "Usage: -dbtimeout [time]";
        options.addOption(Option.builder("dbtimeout").longOpt("dbtimeout")
                .desc(desc).hasArg().argName("dbtimeout").build());

        desc = "Database extras, default nothing.\n" +
                " Usage: -dbextras [extra url get options]";
        options.addOption(Option.builder("dbextras").longOpt("dbextras")
                .desc(desc).hasArg().argName("dbextras").build());
        // Run a check to make sure ChemAxon is enabled.
        desc = "Disable ChemAxon check.\n" +
                " Usage: -nca";
        options.addOption(Option.builder("nca")
                .longOpt("nochemaxon").desc(desc).argName("nochemaxon").build());
        // Chose whether or not you want statistics printed
        desc = "Print statistics regarding this compiler\n" +
                " Usage: -stats";
        options.addOption(Option.builder("stats")
                .longOpt("statistics").desc(desc).hasArg(false).argName("statistics").build());
        // Help
        desc = "print this message.";
        options.addOption(Option.builder("help").longOpt("help").desc(desc).argName("help").build());

        if (addOptionals) {
            // Run SSI Algorithm
            desc = "Run the SSI Algorithm.\n" +
                    "Usage: -ssi";
            options.addOption(Option.builder("ssi").longOpt("ssi")
                    .desc(desc).type(Boolean.class).hasArg(false).required(false)
                    .argName("ssi").build());
            // Enable additional optimizations for compilation.
            desc = "What optimizations to enable." +
                    "\n Available optimizations: " +
                    "\n\t ssi: run SSI algorithm" +
                    "\n\t ssa: run SSA algorithm" +
                    "\n Usage: -opts {list of optimizations}";
            options.addOption(Option.builder("opts").longOpt("optimizations")
                    .desc(desc).hasArgs().required(false)
                    .argName("opts").build());
            // Number of threads in the program
            desc = "Number of threads to use during execution.\n" +
                    "Usage: -threads [number of threads]\n";
            options.addOption(Option.builder("threads").longOpt("threads")
                    .desc(desc).type(Integer.class).hasArg().required(false)
                    .argName("threads").build());
        }

        return options;
    }

    private boolean validateDatabase(CommandLine cmd) {
        if (cmd.hasOption("dbport") || cmd.hasOption("dbaddr") || cmd.hasOption("dbname")) {
            // We only care if we have db flags and no user/pass to accommodate the connection.
            return cmd.hasOption("dbuser") && cmd.hasOption("dbpass");
        }
        // If we have no database flags, we can return true.
        return true;
    }
}
