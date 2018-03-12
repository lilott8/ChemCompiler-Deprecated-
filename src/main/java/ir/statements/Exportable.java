package ir.statements;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Exportable {

    String toJson();

    String toJson(String indent);
}
