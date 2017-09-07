import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;

import compilation.Compiler;
import config.Config;
import config.ConfigFactory;
import simulator.FauxIdentifier;


public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) throws Exception {
        // Build the command line parser
        CommandLine cmd;
        CommandLineParser parser = new DefaultParser();

        // parse the command line relative to the options
        cmd = parser.parse(buildOptions(), args);
        initializeEnvironment(cmd);

        Config config = ConfigFactory.getConfig();

        if (config.isDebug()) {
            logger.info("You are in test mode");
        }

        // Run compilation.
        Compiler compiler = new Compiler(config);
        compiler.compile();
        compiler.runAllOps();
    }

    private static void initializeEnvironment(final CommandLine cmd) throws Exception{
        // see if we asked for help...
        if(cmd.hasOption("help")) {
            HelpFormatter hf = new HelpFormatter();
            hf.printHelp("ChemicalCompiler", buildOptions(), true);
            System.exit(0);
        }

        // See if we have the argument we need.
        if(!cmd.hasOption("compile")) {
            throw new Exception("No input file to compile given.");
        }

        // If we have a translator we must also have output.
        if ((cmd.hasOption("translate") && !cmd.hasOption("output")) || cmd.hasOption("output") && !cmd.hasOption("translate")) {
            throw new Exception("If you provide a translation or an output, the other must accompany.");
        }

        if ((cmd.hasOption("clean") && !cmd.hasOption("output"))) {
            throw new Exception("Attempting to clean output directory, but no directory supplied.");
        }

        if (!validateDatabase(cmd)) {
            throw new Exception("We cannot infer the connection data for the database.");
        }

        // initialize our config object.
        Config config = ConfigFactory.buildConfig(cmd);

        // add any initializing statements derived from the command line here.
        if(config.getFilesForCompilation().size() == 0) {
            throw new Exception("We have no valid files for input");
        }
    }

    /**
     * Builds the command line options needed to run the program
     */
    public static Options buildOptions() {
        Options options = new Options();

        // File(s) to compile
        String desc = "Compile the source file(s)" +
                "\nUsage: -c /path/to/file_to_compile.json";
        options.addOption(Option.builder("c").longOpt("compile")
                .desc(desc).hasArgs().required().type(ArrayList.class)
                .argName("compile").build());

        // Testing mode
        desc = "Debug mode" +
                "\nUsage: -d";
        options.addOption(Option.builder("d").longOpt("debug")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("debug").build());

        // Run SSI Algorithm
        desc = "Run the SSI Algorithm.\nUsage: -ssi";
        options.addOption(Option.builder("ssi").longOpt("ssi")
                .desc(desc).type(Boolean.class).hasArg().required(false)
                .argName("ssi").build());

        // Output file option
        desc = "Place output in which directory.  If -t is set, this must be set." +
                "\n Usage: -o /path/to/output/";
        options.addOption(Option.builder("o").longOpt("output")
                .desc(desc).type(String.class).hasArg().required(false)
                .argName("output").build());

        // What translators to use
        desc = "What translator to use.  If -o is set, this must be set." +
                "\n Usage: -translate {list of translators}" +
                "\n Available translators: " +
                "\n\t mfsim: translates cfg to mfsim machine code" +
                "\n\t typesystem: translates cfg for further typing analysis";
        options.addOption(Option.builder("t").longOpt("translate")
                .desc(desc).type(ArrayList.class).hasArgs().required(false)
                .argName("translate").build());

        desc = "What level to resolve inference at." +
                "\n Usage: -r [union|generic]" +
                "\n default: -r generic";
        options.addOption(Option.builder("r").longOpt("resolve")
                .desc(desc).hasArg().required(false).argName("resolve").build());

        // Clean output option
        desc = "Clean the output directory. If -clean is set, -o (output) must be set." +
                "\nUsage: -clean";
        options.addOption(Option.builder("clean").longOpt("clean")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("clean").build());

        desc = "What phases to enable." +
                "\n Usage: -p {list of phases}" +
                "\n Available phases: " +
                "\n\t inference: run type inference" +
                "\n\t simple: run simple inference";
        options.addOption(Option.builder("p").longOpt("phases")
            .desc(desc).hasArgs().required(false)
            .argName("phases").build());

        // Database name
        desc = "Database name." +
                "\nUsage: -dbname [name]";
        options.addOption(Option.builder("dbname").longOpt("dbname")
                .desc(desc).hasArg().argName("dbname").build());
        // Database user name
        desc = "Database user name." +
                "\nUsage -dbuser [name]";
        options.addOption(Option.builder("dbuser").longOpt("dbuser")
                .desc(desc).hasArg().argName("dbuser").build());
        // Database password
        desc = "Database password." +
                "\nUsage -dbpass [pass]";
        options.addOption(Option.builder("dbpass").longOpt("dbpass")
                .desc(desc).hasArg().argName("dbpass").build());
        // Database port
        desc = "Database port, default: 3306." +
                "\nUsage -dbport [port]";
        options.addOption(Option.builder("dbport").longOpt("dbport")
                .desc(desc).hasArg().argName("dbport").build());
        // Database address
        desc = "Database address, default localhost." +
                "\nUsage -dbaddr [addr]";
        options.addOption(Option.builder("dbaddr").longOpt("dbaddr")
                .desc(desc).hasArg().argName("dbaddr").build());
        // Database driver, e.g. org.mariadb.jdbc.MySQLDataSource
        desc = "Database driver default org.mariadb.jdbc.MySQLDataSource.  " +
                "\nUsage: -dbdriver [driver]";
        options.addOption(Option.builder("dbdriver").longOpt("dbdriver")
                .desc(desc).hasArg().argName("dbdriver").build());
        // Database timeout
        desc = "Database timeout, default 10 seconds." +
                "\nUsage: -dbtimeout [time]";
        options.addOption(Option.builder("dbtimeout").longOpt("dbtimeout")
                .desc(desc).hasArg().argName("dbtimeout").build());

        desc = "Database extras, default nothing." +
                "\n Usage: -dbextras [extra url get options]";
        options.addOption(Option.builder("dbextras").longOpt("dbextras")
                .desc(desc).hasArg().argName("dbextras").build());

        return options;
    }

    private static boolean validateDatabase(CommandLine cmd) {
        if (cmd.hasOption("dbport") || cmd.hasOption("dbaddr") || cmd.hasOption("dbname")) {
            // We only care if we have db flags and no user/pass to accommodate the connection.
            return cmd.hasOption("dbuser") && cmd.hasOption("dbpass");
        }
        // If we have no database flags, we can return true.
        return true;
    }
}
