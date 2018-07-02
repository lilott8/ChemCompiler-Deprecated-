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
        Compiler compiler = new Compiler(config);
        compiler.compile();
        //compiler.runAllOps();
        //logger.debug(compiler.getControlFlow());
        // runner();

        //try {
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/aquacoreassays/neurotransmitter_sensing.json"); /* split only to one node */

            /* confirmed parsing correctly */
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/biocoder/pcr_droplet_replenishment.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/contrived/pcr_probabilistic.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/aquacoreassays/pcr.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/aquacoreassays/glucose_detection.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/aquacoreassays/image_probe_synth.json");
            /* aiha assays all translate properly, but mfsim is expecting names without special symbols */
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/realworld/aiha1.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/realworld/aiha2.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/realworld/aiha3.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/realworld/mustard_gas.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/realworld/safety_zone.json");
            /* elisa assays */
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/dilution.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/broad_spectrum_opiate.json");


            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/ciprofloxacin.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/diazepam.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/fentanyl.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/full_morphine.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/heroine.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/morphine.json");
            //BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/elisa/oxycodone.json");

            /* extra */

            // BenchtopParser.parseFromFile("src/main/resources/tests/deprecated/contrived/pcr_probabilistic.json");
            /* opiate immunoassay positive/false */


        /*}
        catch (FileNotFoundException e) {
            logger.error(e.getMessage());
        }*/
        // Compiler compiler = new Compiler(config);
        // compiler.compile(1);
    }

//    public static void main(String[] args) {
//        // Build the command line parser
//
//
//        /*test*/
//        //aiha1.bs
//          aiha2.bs
//          aiha3.bs
//        /*
//          mustard_gas.bs
//          safety_zone.bs
//          pcr.bs
//          probabilisitc_pcr.bs
//          glucose_detection.bs
//          image_probe_synthesis.bs
//          pcr_droplet_replenishment.bs
//          dilution.bs
//          ....react assays....
//          broad_spectrum_opiate.bs
//          ....
//
//         */
//
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

    public static void runner() {
        List<String> compile = new ArrayList<>();

        // Aquacore Tests. (0-3)
        compile.add("src/main/resources/tests/bioscript/aquacore/glucose_detection.bs");
        compile.add("src/main/resources/tests/bioscript/aquacore/image_probe_synthesis.bs");
        compile.add("src/main/resources/tests/bioscript/aquacore/neurotransmitter_sensing.bs");
        compile.add("src/main/resources/tests/bioscript/aquacore/pcr.bs");

        // Chemtrails Tests. (4-7)
        compile.add("src/main/resources/tests/bioscript/chemtype1.json");
        compile.add("src/main/resources/tests/bioscript/chemtype2.json");
        compile.add("src/main/resources/tests/bioscript/chemtype3.json");
        compile.add("src/main/resources/tests/bioscript/chemtype4.json");

        // Contrived Tests. (8-14)
        compile.add("src/main/resources/tests/contrived/compileFail.json");
        compile.add("src/main/resources/tests/contrived/heat_op.json");
        compile.add("src/main/resources/tests/contrived/if_elif_else.json");
        compile.add("src/main/resources/tests/contrived/if_else.json");
        compile.add("src/main/resources/tests/contrived/simple.json");
        compile.add("src/main/resources/tests/contrived/mix-manual-actuation.json");
        compile.add("src/main/resources/tests/contrived/split.json");

        // Elisa Tests. (15-23)
        compile.add("src/main/resources/tests/bioscript/elisa/broad_spectrum_opiate.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/ciprofloxacin.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/diazepam.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/dilution.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/fentanyl.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/full_morphine.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/heroin.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/morphine.bs");
        compile.add("src/main/resources/tests/bioscript/elisa/oxycodone.bs");

        // Real world Tests. (24-33)
        compile.add("src/main/resources/tests/bioscript/realworld/aiha1.bs");
        compile.add("src/main/resources/tests/bioscript/realworld/aiha2.bs");
        compile.add("src/main/resources/tests/bioscript/realworld/aiha3.bs");
        compile.add("src/main/resources/tests/realworld/fail1.json");
        compile.add("src/main/resources/tests/realworld/fail2.json");
        compile.add("src/main/resources/tests/realworld/fail3.json");
        compile.add("src/main/resources/tests/realworld/mustard_gas.json");
        compile.add("src/main/resources/tests/realworld/pass1.json");
        compile.add("src/main/resources/tests/realworld/pass2.json");
        compile.add("src/main/resources/tests/realworld/safety_zone.json");

        CliWrapper cli;
        Compiler compiler;

        StatisticCombinator.writer.write("typesystem stuff:");
        StatisticCombinator.writer.write("min|max|total|median|average");

        StatisticCombinator.writer.flush();

        // EpaManager.INSTANCE.initialize();
        String c;
        //0-34
        // c = compile.get(0);
        // c = compile.get(1);
        // Cannot run Neurotransmitter
        // c = compile.get(2);
        // Cannot run PCR
        // c = compile.get(3);

        // c = compile.get(4);
        // c = compile.get(5);
        // c = compile.get(6);
        // c = compile.get(7);

        // c = compile.get(8);
        // c = compile.get(9);
        // c = compile.get(10);
        // c = compile.get(11);
        // c = compile.get(12);
        // c = compile.get(13);
        // c = compile.get(14);

        // Elisa Tests.
        // c = compile.get(15);
        // c = compile.get(16);
        // c = compile.get(17);
        // c = compile.get(18);
        // c = compile.get(19);
        // c = compile.get(20);
        // c = compile.get(21);
        // c = compile.get(22);
        c = compile.get(23);

        // Real World Tests.
        // c = compile.get(24);
        // c = compile.get(25);
        // c = compile.get(26);
        // c = compile.get(27);
        // c = compile.get(28);
        // c = compile.get(29);
        // c = compile.get(30);
        // c = compile.get(31);
        // c = compile.get(32);
        // c = compile.get(33);

        //for (String c : compile) {
//        StatisticCombinator.writer.push("=====================================");
//        StatisticCombinator.writer.push(c);
//        long inferenceTime, compileTime, beginTime = 0;
//        logger.info("Running: " + c);
//        String args = String.format("-c %s -ts error " +
//                "%s -d -nf -epadefs src/main/resources/epa.xml -drm -classify 4 -o /Users/jason/Desktop/\n", c, DBArgs.getDBArgs());
//        cli = new CliWrapper();
//        cli.parseCommandLine(StringUtils.split(args));
//
//        compiler = new Compiler(ConfigFactory.getConfig());
//        beginTime = System.nanoTime();
//        compiler.compile();
//        compileTime = System.nanoTime() - beginTime;
//
//        beginTime = System.nanoTime();
//        // compiler.runAllOps();
//        inferenceTime = System.nanoTime() - beginTime;
//
//        StatisticCombinator.writer.push("compile time: " + compileTime);
//        StatisticCombinator.writer.push("typesystem time: " + inferenceTime);
//
//        StatisticCombinator.writer.push("=====================================");
//        StatisticCombinator.writer.flush();
//        //}
//        StatisticCombinator.writer.sendDoneSignal();
    }
}
