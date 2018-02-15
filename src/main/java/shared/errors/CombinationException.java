package shared.errors;

/**
 * Thrown when 2 chemicals cannot be combined, the context is that
 * we cannot mix two compounds together, i.e. the compounds might not
 * have free hydrogens to attach to.
 */
public class CombinationException extends ChemTrailsException {

    public CombinationException(String message) {
        super(message);
    }

    public CombinationException(String message, Exception e) {
        super(message, e);
    }

}
