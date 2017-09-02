package inference;

import org.junit.Test;

import static org.junit.Assert.assertTrue;
import static utils.CommonUtils.runTest;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ContrivedTest {

    public static String root = "src/main/resources/tests/contrived/";

    @Test
    public void heatOpSimpleSat() {
        String file = "heat_op.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void ifElifElseSimpleSat() {
        String file = "if_elif_else.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void ifElseSimpleSat() {
        String file = "if_else.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void mixOpSimpleSat() {
        String file = "mix_op.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void simpleSimpleSat() {
        String file = "simple.json";
        assertTrue(runTest(root + file));
    }

    @Test
    public void simpleMixSimpleSat() {
        String file = "simple_mix.json";
        assertTrue(runTest(root + file));
    }
}
