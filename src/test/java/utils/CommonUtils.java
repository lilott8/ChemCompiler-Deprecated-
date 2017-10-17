package utils;

import com.sun.tools.javac.comp.Infer;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;

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
        String args = String.format("-c %s -p inference " +
                //"-dbname chem_trails -dbuser root -dbpass root " +
                //"-dbextras ?useJDBCCompliantTimezoneShift=true&useLegacyDatetimeCode=false&serverTimezone=UTC&useSSL=false " +
                "-d -nf -i -classify 16\n", file);
        CliWrapper cli = new CliWrapper();
        cli.parseCommandLine(StringUtils.split(args));
        //LogManager.getLogger(CommonUtils.class).info(ConfigFactory.getConfig().getFilesForCompilation());
        Compiler compiler = new Compiler(ConfigFactory.getConfig());
        compiler.compile();
        Inference inference = new Inference();
        compiler.runAllOps();
        // We can do this because the test has only one experiment!
        return inference.runPhase(compiler.getExperiments().get(0));
    }
}
