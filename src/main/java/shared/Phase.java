package shared;

/**
 * @created: 1/30/18
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * A phase handles a large portion of compilation.
 * It is usually comprised of multiple steps, e.g.:
 *  Parsing -> [lexical analysis, ast generation, type checking]
 *  Data Flow -> [liveliness analysis, control flow, etc]
 */
public interface Phase {

    Phase run();

    String getName();
}
