package utils;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.lang3.StringUtils;

import java.lang.reflect.Method;

import cli.CliWrapper;
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

    public static boolean runTest(String file) {
        String args = String.format("-c %s -p inference", file);
        CliWrapper cli = new CliWrapper();
        try {
            cli.parseCommandLine(StringUtils.split(args));
        } catch(Exception e){}
        // TODO: run the phases here.
        Compiler compiler = new Compiler(ConfigFactory.getConfig());
        compiler.compile();
        Inference inference = new Inference();
        // We can do this because the test has only one experiment!
        return inference.runPhase(compiler.getExperiments().get(0));
    }
}
