package compiler;

import org.apache.commons.lang3.StringUtils;
import org.junit.Test;

import cli.CliWrapper;
import compilation.Compiler;
import compilation.symboltable.UsageGovernor;
import config.ConfigFactory;
import shared.errors.UsageException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static utils.CommonUtils.runTest;

/**
 * @created: 6/27/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class UsageTest {

    public static final String baseCommand = "-ts none -d -nf -classify 0 -o ./ -c ";
    public static String root = "src/main/resources/tests/usage/";
    private final CliWrapper cli = new CliWrapper();
    private Compiler compiler;

    @Test
    public void passReassign() {
        String file = "reassign_pass.bs";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        UsageGovernor.reset();
    }

    @Test
    public void passGlobal() {
        String file = "global_pass.bs";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        UsageGovernor.reset();
    }

    @Test(expected = UsageException.class)
    public void failGlobal() {
        String file = "global_fail.bs";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        UsageGovernor.reset();
    }

    @Test(expected = UsageException.class)
    public void failLocal() {
        String file = "local_fail.bs";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        UsageGovernor.reset();
    }

    @Test
    public void passLocal() {
        String file = "local_pass.bs";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        UsageGovernor.reset();
    }
}
