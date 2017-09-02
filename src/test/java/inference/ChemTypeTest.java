package inference;

import org.junit.Test;

import static org.junit.Assert.assertTrue;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemTypeTest {

    public static String root = "src/main/resources/tests/chemtype/";

    @Test
    public void chemType1SimpleSat() {
        String file = "chemtype1.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void chemType2SimpleSat() {
        String file = "chemtype2.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void chemType3SimpleSat() {
        String file = "chemtype3.json";
        assertTrue(runTest(root + file));
    }
}
