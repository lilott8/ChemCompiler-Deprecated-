import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SimpleTest {
    protected static final Logger logger = LogManager.getLogger(SimpleTest.class);

    @Test
    public void initTest() {
        logger.info("Just testing stuff");
    }
}
