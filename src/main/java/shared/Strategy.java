package shared;

/**
 * @created: 1/30/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Strategy {
    String getName();

    Strategy run();
}
