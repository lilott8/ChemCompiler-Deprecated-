import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import typesystem.AquaCoreAssayTest;
import typesystem.ChemTypeTest;
import typesystem.ContrivedTest;
import typesystem.ElisaTest;
import typesystem.InferenceSuite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
    InferenceSuite.class
})
public class MainTest {}
