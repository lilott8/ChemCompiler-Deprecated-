package shared.errors;

import org.apache.logging.log4j.LogManager;

/**
 * @created: 10/19/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class UsageException extends ChemTrailsException {

    public UsageException(String message) {
        super(message);
        LogManager.getLogger(UsageException.class).fatal(message + "\n Exiting in UsageException.");
        //System.exit(0);
    }

    public UsageException(String message, Exception e) {
        super(message, e);
    }
}
