package ir;

import java.util.List;

import shared.variable.Variable;

/**
 * @created: 3/20/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
interface Convertable {
    void alphaConversion(List<Variable> parameters);
}
