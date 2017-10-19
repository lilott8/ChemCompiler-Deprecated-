package inference;

import org.junit.Test;

import errors.CompatabilityException;

import static org.junit.Assert.assertFalse;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemTypeTest {

    public static String root = "src/main/resources/tests/chemtype/";

    /**
     * The following tests will fail in the "mix" stage.
     */
    @Test(expected = CompatabilityException.class)
    public void chemType1SimpleException() {
        String file = "chemtype1.json";
        assertFalse(runTest(root + file));
    }

    @Test(expected = CompatabilityException.class)
    public void chemType2SimpleException() {
        String file = "chemtype2.json";
        assertFalse(runTest(root + file));
    }

    @Test(expected = CompatabilityException.class)
    public void chemType3SimpleException() {
        String file = "chemtype3.json";
        assertFalse(runTest(root + file));
    }

    /**
     * The following tests will fail in the SAT stage.
     */
    @Test
    public void chemType1SimpleUnsat() {
        String file = "chemtype1.json";
        assertFalse(runTest(root + file));
    }

    @Test
    public void chemType2SimpleUnsat() {
        String file = "chemtype2.json";
        assertFalse(runTest(root + file));
    }

    @Test
    public void chemTypes3SimpleUnsat() {
        String file = "chemtype3.json";
        assertFalse(runTest(root + file));
    }
}
