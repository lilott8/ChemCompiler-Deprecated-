package errors;

/**
 * This is a generic parent exception for all other exceptions in this program
 */
public class ChemTrailsException extends RuntimeException {

    public ChemTrailsException(String message) {
        super(message);
    }

    public ChemTrailsException(String message, Exception e) {
        super(message, e);
    }
}
