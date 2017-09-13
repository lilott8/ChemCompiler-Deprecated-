package typesystem.combinator;

import shared.substances.BaseCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Combiner {

    BaseCompound combine(BaseCompound a, BaseCompound b);
}
