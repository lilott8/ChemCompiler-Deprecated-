package shared.errors;

/**
 * Thrown when 2 compounds mixed together will result in an adverse reaction
 */
public class CompatabilityException extends ChemTrailsException {

    public CompatabilityException(String message) {
        super(message);
    }

    public CompatabilityException(String message, Exception e) {
        super(message, e);
    }

}
