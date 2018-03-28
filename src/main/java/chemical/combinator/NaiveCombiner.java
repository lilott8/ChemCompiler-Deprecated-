package chemical.combinator;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveCombiner implements Combiner {

    NaiveCombiner() {
    }

    @Override
    public Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b) {
        a.addAll(b);

        List<ChemTypes> listA = new ArrayList<>();
        List<ChemTypes> listB = new ArrayList<>();

        listA.addAll(a);
        listB.addAll(b);

        this.combine(a, b);

        return a;
    }
}
