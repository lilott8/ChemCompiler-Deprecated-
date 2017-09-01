package inference;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
        AquaCoreAssayTest.class,
        ChemTypeTest.class,
        ContrivedTest.class,
        ElisaTest.class
})
public class InferenceSuite {}
