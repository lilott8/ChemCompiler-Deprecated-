package utils;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.lang3.StringUtils;

import java.lang.reflect.Method;

import compilation.Compiler;
import config.Config;
import config.ConfigFactory;
import phases.inference.Inference;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CommonUtils {

    private static CommandLine buildCommandLine(String args) {
        try {
            return new DefaultParser().parse(getOptionsFromMain(), StringUtils.split(args, " "));
        } catch(Exception e) {}
        return null;
    }

    private static Options getOptionsFromMain() {
        try {
            Class<?> c = Class.forName("Main");
            Object t = c.newInstance();

            for (Method m : c.getDeclaredMethods()) {
                // Note the second string *must* match with the declaration in Main.
                if (StringUtils.equalsIgnoreCase(m.getName(), "buildoptions")) {
                    m.setAccessible(true);
                    return (Options) m.invoke(t);
                }
            }
        } catch(Exception e) {

        }
        return new Options();
    }

    public static boolean runTest(String file) {
        String args = String.format("-c %s -p inference", file);
        CommandLine cmd = CommonUtils.buildCommandLine(args);
        Config config = ConfigFactory.buildConfig(cmd);
        // TODO: run the phases here.
        Compiler compiler = new Compiler(config);
        compiler.compile();
        Inference inference = new Inference();
        // We can do this because the test has only one experiment!
        return inference.runPhase(compiler.getExperiments().get(0));
    }
}
