package inference;

import org.junit.Test;

import static org.junit.Assert.assertTrue;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class AquaCoreAssayTest {

    public static String root = "src/main/resources/tests/aquacoreassays/";

    @Test
    public void glucoseDetectionSimpleSat() {
        String file = "glucose_detection.json";
        //assertTrue(runTest(root + file));
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
