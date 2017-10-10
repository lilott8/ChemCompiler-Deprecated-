package inference;

import org.junit.Test;

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

    public static String root = "src/main/resources/tests/aquacoreassays/";
    public static String baseCommand = "-p inference " +
            "-dbname chem_trails -dbuser root -dbpass root " +
            "-dbextras ?useJDBCCompliantTimezoneShift=true&useLegacyDatetimeCode=false&serverTimezone=UTC&useSSL=false " +
            "-d -nf -i -classify 16 -c ";

    @Test
    public void glucoseDetectionSimpleSat() {
        String file = "glucose_detection.json";

        Compiler compiler = new Compiler(ConfigFactory.getConfig());
        compiler.compile();
        Inference inference = new Inference();
        inference.runPhase(compiler.getExperiments().get(0));
        assertTrue(runTest(baseCommand + root + file));

        if (1 == 1) {
            
        }
    }

    @Test
    public void imageProbeSynthSimpleSat() {
        String file = "image_probe_synth.json";
        //assertTrue(runTest(root + file));
    }

    @Test
    public void neuroTransmitterSensingSimpleSat() {
        String file = "neurotransmitter_sensing.json";
        //assertTrue(runTest(root + file));
    }

    @Test
    public void pcrSimpleSat() {
        String file = "pcr.json";
        //assertTrue(runTest(root + file));
    }
}
