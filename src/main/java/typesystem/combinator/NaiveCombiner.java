package typesystem.combinator;

import com.fasterxml.jackson.databind.ser.Serializers;

import java.util.Set;

import shared.substances.BaseCompound;
import shared.substances.NaiveCompound;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveCombiner implements Combiner {

    NaiveCombiner() {}

    @Override
    public BaseCompound combine(BaseCompound a, BaseCompound b) {
        BaseCompound compound = new NaiveCompound(-1);
        compound.addReactiveGroup(a.getReactiveGroups());
        compound.addReactiveGroup(b.getReactiveGroups());
        return compound;
    }

    @Override
    public Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b) {
        a.addAll(b);
        return a;
    }
}
