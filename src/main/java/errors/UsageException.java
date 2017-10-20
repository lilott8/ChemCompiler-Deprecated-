package errors;

/**
 * @created: 10/19/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class UsageException extends ChemTrailsException {

    public UsageException(String message) {
        super(message);
    }

    public UsageException(String message, Exception e) {
        super(message, e);
    }
}
