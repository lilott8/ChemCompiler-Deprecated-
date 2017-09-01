import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import inference.AquaCoreAssayTest;
import inference.ChemTypeTest;
import inference.ContrivedTest;
import inference.ElisaTest;
import inference.InferenceSuite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
    InferenceSuite.class
})
public class MainTest {}
