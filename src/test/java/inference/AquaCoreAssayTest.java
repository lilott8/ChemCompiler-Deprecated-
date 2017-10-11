package inference;

import org.apache.commons.lang3.StringUtils;
import org.junit.Test;

import cli.CliWrapper;
import compilation.Compiler;
import config.ConfigFactory;
import phases.inference.Inference;

import static org.junit.Assert.assertTrue;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class AquaCoreAssayTest {

    public static final String root = "src/main/resources/tests/aquacoreassays/";
    public static final String baseCommand = "-p inference " +
            "-dbname chem_trails -dbuser root -dbpass root " +
            "-dbextras ?useJDBCCompliantTimezoneShift=true&useLegacyDatetimeCode=false&serverTimezone=UTC&useSSL=false " +
            "-d -nf -i -classify 16 -c ";

    private final CliWrapper cli = new CliWrapper();
    private Compiler compiler;

    @Test
    public void glucoseDetectionSimpleSat() {
        String file = "glucose_detection.json";
        //cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        //this.compiler = new Compiler(ConfigFactory.getConfig());
        //this.compiler.compile();
        //Inference inference = new Inference();
        //assertTrue(inference.runPhase(compiler.getExperiments().get(0)));
        assertTrue(runTest(root + file));
    }

    @Test
    public void imageProbeSynthSimpleSat() {
        String file = "image_probe_synth.json";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        Inference inference = new Inference();
        inference.runPhase(compiler.getExperiments().get(0));
        assertTrue(runTest(root + file));
    }

    @Test
    public void neuroTransmitterSensingSimpleSat() {
        String file = "neurotransmitter_sensing.json";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        Inference inference = new Inference();
        inference.runPhase(compiler.getExperiments().get(0));
        assertTrue(runTest(root + file));
    }

    @Test
    public void pcrSimpleSat() {
        String file = "pcr.json";
        cli.parseCommandLine(StringUtils.split(baseCommand + root + file));
        this.compiler = new Compiler(ConfigFactory.getConfig());
        this.compiler.compile();
        Inference inference = new Inference();
        inference.runPhase(compiler.getExperiments().get(0));
        assertTrue(runTest(root + file));
    }
}
