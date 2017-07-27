import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import CompilerDataStructures.ControlFlowGraph.CFG;
import Translators.MFSimSSA.MFSimSSATranslator;
import manager.Benchtop;
import parsing.BioScript.BenchtopParser;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CompilationSequence {

    public static final Logger logger = LogManager.getLogger(CompilationSequence.class);

    public static Compiler compile(String file) {
        try {
            BenchtopParser.parse(CompilationSequence.class.getClassLoader().getResource(file).getPath());
            return new Compiler(Benchtop.INSTANCE);
        }
        catch (Exception e) {
            logger.fatal(e.getMessage());
            logger.fatal(e.getStackTrace());
        }
        return null;
    }
}
