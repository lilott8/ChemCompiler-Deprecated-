import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import compiler.CompilerSuite;
import typesystem.AquaCoreAssayTest;
import typesystem.ChemTypeTest;
import typesystem.ContrivedTest;
import typesystem.ElisaTest;
import typesystem.InferenceSuite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        CompilerSuite.class
        //InferenceSuite.class
})
public class MainTest {}
