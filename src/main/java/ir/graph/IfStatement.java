package ir.graph;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class IfStatement extends BaseConditional {

    public static final Logger logger = LogManager.getLogger(IfStatement.class);

    public static final String INSTRUCTION = "IF";

    public IfStatement(String condition) {
        super(INSTRUCTION, condition);
        logger.warn("Why is the condition coming in as a string?");
    }
}
