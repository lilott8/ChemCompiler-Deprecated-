package shared.errors;

/**
 * @created: 3/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InvalidSyntaxException extends ChemTrailsException {
    public InvalidSyntaxException(String message) {
        super(message);
    }

    public InvalidSyntaxException(String message, Exception e) {
        super(message, e);
    }
}
