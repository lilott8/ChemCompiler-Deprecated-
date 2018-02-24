package shared.variable;

import symboltable.Scope;

/**
 * @created: 2/23/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface ScopedVariable {

    Scope getScope();
    void addScope(Scope scope);
    String getScopedName();
}
