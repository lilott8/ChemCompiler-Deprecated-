import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import cli.CliWrapper;
//import cli.DBArgs;
import compilation.Compiler;
import config.Config;
import config.ConfigFactory;
import parsing.BioScript.BenchtopParser;
import reactivetable.StatisticCombinator;


public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) {
        // Build the command line parser
        CliWrapper cli = new CliWrapper();
        cli.parseCommandLine(args);

        Config config = ConfigFactory.getConfig();

        if (config.isDebug()) {
            logger.info("You are in debug mode");
        }
        // Run compilation.
        try {
            BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/biocoder/pcr_droplet_replenishment.json");
        }
        catch (FileNotFoundException e) {
            logger.error(e.getMessage());
        }
        Compiler compiler = new Compiler(config);
        compiler.compile(1);
    }

//    public static void main(String[] args) {
//        // Build the command line parser
//        CliWrapper cli = new CliWrapper();
//        cli.parseCommandLine(args);
//
//        Config config = ConfigFactory.getConfig();
//
//        if (config.isDebug()) {
//            logger.info("You are in debug mode");
//        }
//
//        // Run compilation.
//        Compiler compiler = new Compiler(config);
//        compiler.compile();
//    }

    public static final void abandonShip(String message) throws Exception {
        throw new Exception(message);
    }

//    public static void runner() {
//        List<String> compile = new ArrayList<>();
//
//        // Aquacore Tests. (0-3)
//        compile.add("src/main/resources/tests/aquacoreassays/glucose_detection.json");
//        compile.add("src/main/resources/tests/aquacoreassays/image_probe_synth.json");
//        compile.add("src/main/resources/tests/aquacoreassays/neurotransmitter_sensing.json");
//        compile.add("src/main/resources/tests/aquacoreassays/pcr.json");
//
//        // Chemtrails Tests. (4-7)
//        compile.add("src/main/resources/tests/chemtype/chemtype1.json");
//        compile.add("src/main/resources/tests/chemtype/chemtype2.json");
//        compile.add("src/main/resources/tests/chemtype/chemtype3.json");
//        compile.add("src/main/resources/tests/chemtype/chemtype4.json");
//
//        // Contrived Tests. (8-14)
//        compile.add("src/main/resources/tests/contrived/compileFail.json");
//        compile.add("src/main/resources/tests/contrived/heat_op.json");
//        compile.add("src/main/resources/tests/contrived/if_elif_else.json");
//        compile.add("src/main/resources/tests/contrived/if_else.json");
//        compile.add("src/main/resources/tests/contrived/simple.json");
//        compile.add("src/main/resources/tests/contrived/mix-manual-actuation.json");
//        compile.add("src/main/resources/tests/contrived/split.json");
//
//        // Elisa Tests. (15-23)
//        compile.add("src/main/resources/tests/elisa/broad_spectrum_opiate.json");
//        compile.add("src/main/resources/tests/elisa/ciprofloxacin.json");
//        compile.add("src/main/resources/tests/elisa/diazepam.json");
//        compile.add("src/main/resources/tests/elisa/dilution.json");
//        compile.add("src/main/resources/tests/elisa/fentanyl.json");
//        compile.add("src/main/resources/tests/elisa/full_morphine.json");
//        compile.add("src/main/resources/tests/elisa/heroine.json");
//        compile.add("src/main/resources/tests/elisa/morphine.json");
//        compile.add("src/main/resources/tests/elisa/oxycodone.json");
//
//        // Real world Tests. (24-33)
//        compile.add("src/main/resources/tests/realworld/aiha1.json");
//        compile.add("src/main/resources/tests/realworld/aiha2.json");
//        compile.add("src/main/resources/tests/realworld/aiha3.json");
//        compile.add("src/main/resources/tests/realworld/fail1.json");
//        compile.add("src/main/resources/tests/realworld/fail2.json");
//        compile.add("src/main/resources/tests/realworld/fail3.json");
//        compile.add("src/main/resources/tests/realworld/mustard_gas.json");
//        compile.add("src/main/resources/tests/realworld/pass1.json");
//        compile.add("src/main/resources/tests/realworld/pass2.json");
//        compile.add("src/main/resources/tests/realworld/safety_zone.json");
//
//        CliWrapper cli;
//        Compiler compiler;
//
//        StatisticCombinator.writer.write("typesystem stuff:");
//        StatisticCombinator.writer.write("min|max|total|median|average");
//
//        StatisticCombinator.writer.flush();
//
//        // EpaManager.INSTANCE.initialize();
//        String c;
//        //0-34
//        // c = compile.get(0);
//        // c = compile.get(1);
//        // c = compile.get(2);
//        c = compile.get(3);
//
//        // c = compile.get(4);
//        // c = compile.get(5);
//        // c = compile.get(6);
//        // c = compile.get(7);
//
//        // c = compile.get(8);
//        // c = compile.get(9);
//        // c = compile.get(10);
//        // c = compile.get(11);
//        // c = compile.get(12);
//        // c = compile.get(13);
//        // c = compile.get(14);
//
//        // Elisa Tests.
//        // c = compile.get(15);
//        // c = compile.get(16);
//        // c = compile.get(17);
//        // c = compile.get(18);
//        // c = compile.get(19);
//        // c = compile.get(20);
//        // c = compile.get(21);
//        // c = compile.get(22);
//        // c = compile.get(23);
//
//        // Real World Tests.
//        // c = compile.get(24);
//        // c = compile.get(25);
//        // c = compile.get(26);
//        // c = compile.get(27);
//        // c = compile.get(28);
//        // c = compile.get(29);
//        // c = compile.get(30);
//        // c = compile.get(31);
//        // c = compile.get(32);
//        // c = compile.get(33);
//
//        //for (String c : compile) {
//        StatisticCombinator.writer.push("=====================================");
//        StatisticCombinator.writer.push(c);
//        long inferenceTime, compileTime, beginTime = 0;
//        logger.info("Running: " + c);
//        //String args = String.format("-c %s -p typesystem " +
//        //        "%s -d -nf -i -drm -classify 16 -o /Users/jason/Desktop/\n", c, DBArgs.getDBArgs());
//        cli = new CliWrapper();
//        cli.parseCommandLine(StringUtils.split(args));
//
//        compiler = new Compiler(ConfigFactory.getConfig());
//        beginTime = System.nanoTime();
//        compiler.compile();
//        compileTime = System.nanoTime() - beginTime;
//
//        beginTime = System.nanoTime();
//        compiler.runAllOps();
//        inferenceTime = System.nanoTime() - beginTime;
//
//        StatisticCombinator.writer.push("compile time: " + compileTime);
//        StatisticCombinator.writer.push("typesystem time: " + inferenceTime);
//
//        StatisticCombinator.writer.push("=====================================");
//        StatisticCombinator.writer.flush();
//        //}
//        StatisticCombinator.writer.sendDoneSignal();
//    }
}
