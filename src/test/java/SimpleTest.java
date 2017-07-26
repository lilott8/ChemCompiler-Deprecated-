import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SimpleTest {
    private static final Logger logger = LogManager.getLogger(SimpleTest.class);
    private Compiler compiler;

    @Before
    public void init() {
        this.compiler = CompilationSequence.compile("tests/simple.json");
    }

    @Test
    public void runSimple() {
        //logger.info(this.compiler.toString());
    }
}
