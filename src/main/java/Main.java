import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import cli.CliWrapper;
import compilation.Compiler;
import config.Config;
import config.ConfigFactory;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;


public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) throws Exception {
        // Build the command line parser
        CliWrapper cli = new CliWrapper();
        cli.parseCommandLine(args);

        Config config = ConfigFactory.getConfig();

        if (config.isDebug()) {
            logger.info("You are in test mode");
        }

        // Run compilation.
        Compiler compiler = new Compiler(config);
        compiler.compile();
        compiler.runAllOps();
        logger.debug(compiler.getControlFlow());
    }
}
