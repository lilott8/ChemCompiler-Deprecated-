package inference;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import static org.junit.Assert.*;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class  ElisaTest {

    public static String root = "src/main/resources/tests/elisa/";
    public static final Logger logger = LogManager.getLogger(ElisaTest.class);

    @Test
    public void broadSpectrumOpiateSat() {
        String file = "broad_spectrum_opiate.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void ciprofloxacinSat() {
        String file = "ciprofloxacin.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void diazepamSat() {
        String file = "diazepam.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void dilutionSat() {
        String file = "dilution.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void fentanylSat() {
        String file = "fentanyl.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void fullMorphineSat() {
        String file = "full_morphine.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void heroineSat() {
        String file = "heroine.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void morphineSat() {
        String file = "morphine.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void oxycodoneSat() {
        String file = "oxycodone.json";
        assertTrue(runTest(root + file));
    }
}
