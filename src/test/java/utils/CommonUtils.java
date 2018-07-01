package utils;

import org.apache.commons.lang3.StringUtils;

import cli.CliWrapper;
import compilation.Compiler;
import config.ConfigFactory;
import typesystem.Inference;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CommonUtils {

    public static boolean runTest(String file) {
        String args = String.format("-c %s -p typesystem " +
                "%s " +
                //"-d -nf -i -classify 16\n", file, DBArgs.getDBArgs());
        "");
        CliWrapper cli = new CliWrapper();
        cli.parseCommandLine(StringUtils.split(args));
        //LogManager.getLogger(CommonUtils.class).info(ConfigFactory.getConfig().getFilesForCompilation());
        Compiler compiler = new Compiler(ConfigFactory.getConfig());
        compiler.compile();
        Inference inference = new Inference();
        compiler.runAllOps();
        // We can do this because the elisa has only one experiment!
        return inference.runPhase(compiler.getExperiments().get(0));
    }
}
