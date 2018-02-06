package shared;

/**
 * @created: 1/30/18
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * A step is a smaller portion of the phase it resides in.
 * It does smaller, discrete portions of work that may,
 * or may not, be dependent upon each other.
 */
public interface Step {

    Step run();

    String getName();
}
