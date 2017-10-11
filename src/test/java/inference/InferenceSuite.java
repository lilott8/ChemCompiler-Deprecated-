package inference;

import org.apache.commons.cli.CommandLine;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import compilation.Compiler;
import config.Config;
import config.ConfigFactory;
import phases.inference.Inference;
import utils.CommonUtils;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
        ChemTypeTest.class,
        ContrivedTest.class,
        AquaCoreAssayTest.class,
        ElisaTest.class
})
public class InferenceSuite {}
