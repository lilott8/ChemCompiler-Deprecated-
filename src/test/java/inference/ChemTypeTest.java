package inference;

import org.junit.Test;

import errors.CompatabilityException;

import static org.junit.Assert.*;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemTypeTest {

    public static String root = "src/main/resources/tests/chemtype/";

    @Test(expected = CompatabilityException.class)
    public void chemType1SimpleSat() {
        String file = "chemtype1.json";
        assertFalse(runTest(root + file));
    }

    @Test(expected = CompatabilityException.class)
    public void chemType2SimpleSat() {
        String file = "chemtype2.json";
        assertFalse(runTest(root + file));
    }

    @Test(expected = CompatabilityException.class)
    public void chemType3SimpleSat() {
        String file = "chemtype3.json";
        assertFalse(runTest(root + file));
    }
}
