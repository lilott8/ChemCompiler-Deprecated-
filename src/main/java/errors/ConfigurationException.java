package errors;

/**
 * @created: 10/10/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ConfigurationException extends ChemTrailsException {
    public ConfigurationException(String message) {
        super(message);
    }

    public ConfigurationException(String message, Exception e) {
        super(message, e);
    }
}
