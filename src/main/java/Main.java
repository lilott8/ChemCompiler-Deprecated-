import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.List;

import cli.CliWrapper;
import cli.DBArgs;
import compilation.Compiler;
import config.Config;
import config.ConfigFactory;
import shared.Delete;
import typesystem.epa.EpaManager;


public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) throws Exception {
        // Build the command line parser
        CliWrapper cli = new CliWrapper();
        cli.parseCommandLine(args);

        Config config = ConfigFactory.getConfig();

        if (config.isDebug()) {
            logger.info("You are in debug mode");
        }

        // Run compilation.
        //Compiler compiler = new Compiler(config);
        //compiler.compile();
        //compiler.runAllOps();
        //logger.debug(compiler.getControlFlow());
        runner();
    }

    public static void runner() throws Exception {
        List<String> compile = new ArrayList<>();

        // Aquacore Tests.
        compile.add("src/main/resources/tests/aquacoreassays/glucose_detection.json");
        compile.add("src/main/resources/tests/aquacoreassays/image_probe_synth.json");
        compile.add("src/main/resources/tests/aquacoreassays/neurotransmitter_sensing.json");
        compile.add("src/main/resources/tests/aquacoreassays/pcr.json");

        // Chemtrails Tests.
        compile.add("src/main/resources/tests/chemtype/chemtype1.json");
        compile.add("src/main/resources/tests/chemtype/chemtype2.json");
        compile.add("src/main/resources/tests/chemtype/chemtype3.json");
        compile.add("src/main/resources/tests/chemtype/chemtype4.json");

        // Contrived Tests.
        compile.add("src/main/resources/tests/contrived/compileFail.json");
        compile.add("src/main/resources/tests/contrived/heat_op.json");
        compile.add("src/main/resources/tests/contrived/if_elif_else.json");
        compile.add("src/main/resources/tests/contrived/if_else.json");
        compile.add("src/main/resources/tests/contrived/simple.json");
        compile.add("src/main/resources/tests/contrived/simple_mix.json");
        compile.add("src/main/resources/tests/contrived/split.json");

        // Elisa Tests.
        compile.add("src/main/resources/tests/elisa/broad_spectrum_opiate.json");
        compile.add("src/main/resources/tests/elisa/ciprofloxacin.json");
        compile.add("src/main/resources/tests/elisa/diazepam.json");
        compile.add("src/main/resources/tests/elisa/dilution.json");
        compile.add("src/main/resources/tests/elisa/fentanyl.json");
        compile.add("src/main/resources/tests/elisa/full_morphine.json");
        compile.add("src/main/resources/tests/elisa/heroine.json");
        compile.add("src/main/resources/tests/elisa/morphine.json");
        compile.add("src/main/resources/tests/elisa/oxycodone.json");

        compile.add("src/main/resources/tests/realworld/aiha1.json");
        compile.add("src/main/resources/tests/realworld/aiha2.json");
        compile.add("src/main/resources/tests/realworld/aiha3.json");
        compile.add("src/main/resources/tests/realworld/fail1.json");
        compile.add("src/main/resources/tests/realworld/fail2.json");
        compile.add("src/main/resources/tests/realworld/fail3.json");
        compile.add("src/main/resources/tests/realworld/mustard_gas.json");
        compile.add("src/main/resources/tests/realworld/pass1.json");
        compile.add("src/main/resources/tests/realworld/pass2.json");
        compile.add("src/main/resources/tests/realworld/safety_zone.json");

        CliWrapper cli;
        Compiler compiler;

        // Delete.writer.write("inference stuff:");
        // Delete.writer.write("min|max|total|median|average");

        Delete.writer.flush();

        EpaManager.INSTANCE.initialize();

        //0-34
        // String c = compile.get(0);
        // String c = compile.get(1);
        // String c = compile.get(2);
        // String c = compile.get(3);
        // String c = compile.get(4);
        // String c = compile.get(5);
        // String c = compile.get(6);
        // String c = compile.get(7);
        // String c = compile.get(8);
        // String c = compile.get(9);
        // String c = compile.get(10);
        // String c = compile.get(11);
        // String c = compile.get(12);
        // String c = compile.get(13);
        // String c = compile.get(14);
        // String c = compile.get(15);
        // String c = compile.get(16);
        // String c = compile.get(17);
        // String c = compile.get(18);
        // String c = compile.get(19);
        // String c = compile.get(20);
        // String c = compile.get(21);
        // String c = compile.get(22);
        // String c = compile.get(23);
        // String c = compile.get(24);
        // Start here when the new experiments are done
        String c = compile.get(25);
        // String c = compile.get(26);
        // String c = compile.get(27);
        // String c = compile.get(28);
        // String c = compile.get(29);
        // String c = compile.get(30);
        // String c = compile.get(31);
        // String c = compile.get(32);
        // String c = compile.get(33);
        // String c = compile.get(34);

        Delete.writer.push("=====================================");
        Delete.writer.push(c);
        long inferenceTime, compileTime, beginTime = 0;
        logger.info("Running: " + c);
        String args = String.format("-c %s -p inference " +
                "%s -d -nf -i -drm -classify 16 -o /Users/jason/Desktop/\n", c, DBArgs.getDBArgs());
        cli = new CliWrapper();
        cli.parseCommandLine(StringUtils.split(args));

        compiler = new Compiler(ConfigFactory.getConfig());
        beginTime = System.nanoTime();
        compiler.compile();
        compileTime = System.nanoTime() - beginTime;

        beginTime = System.nanoTime();
        compiler.runAllOps();
        inferenceTime = System.nanoTime() - beginTime;

        Delete.writer.push("compile time: " + compileTime);
        Delete.writer.push("inference time: " + inferenceTime);

        Delete.writer.push("=====================================");
        Delete.writer.flush();
        Delete.writer.sendDoneSignal();
    }
}
