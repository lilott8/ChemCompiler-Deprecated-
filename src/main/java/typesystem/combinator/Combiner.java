package typesystem.combinator;

import java.util.Set;

import shared.substances.BaseCompound;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Combiner {

    BaseCompound combine(BaseCompound a, BaseCompound b);
    Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b);
}
