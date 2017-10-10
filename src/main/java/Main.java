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
        CommandLine cmd;
        CommandLineParser parser = new DefaultParser();

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
    }

    public static void main2() {
        logger.fatal("This was used to simulate the illegal combinations manifest in the EPAManager class");
        StringBuilder sb = new StringBuilder();
        Random random = new Random();
        List<ChemTypes> chems = new ArrayList<>(ChemTypes.getIntegerChemTypesMap().values());
        int lower = 0;
        int upper = chems.size()-1;

        for(Map.Entry<Integer, ChemTypes> t : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("put(").append(t.getValue()).append(", new HashSet<ChemTypes>() {{");
            // We can select any amount from 0 to all of the things.
            int iterateTo = random.nextInt(upper - (random.nextInt(upper-lower)+lower) + lower);
            Set<ChemTypes> toAdd = new HashSet<>();
            for (int x = 0; x < iterateTo; x++) {
                int append = random.nextInt(upper - (random.nextInt(upper-lower)+lower) + lower);
                toAdd.add(chems.get(append));
            }
            for (ChemTypes x : toAdd) {
                sb.append("add(").append(x).append(")").append("; ");
            }
            sb.append("}};);").append(System.lineSeparator());
        }
    }
}
