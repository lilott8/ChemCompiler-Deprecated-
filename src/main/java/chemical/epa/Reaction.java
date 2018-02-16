package chemical.epa;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Reaction {

    private EnumSet<Consequence> consequences;

    public Reaction(Consequence... c) {
        consequences = EnumSet.copyOf(Arrays.asList(c));
    }

    public Reaction(List<Consequence> c) {
        consequences = EnumSet.copyOf(c);
    }

    public Set<Consequence> getConsequences() {
        return consequences;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Reaction)) {
            return false;
        }

        Reaction reaction = (Reaction) o;

        return consequences.equals(reaction.consequences);

    }

    @Override
    public int hashCode() {
        return consequences.hashCode();
    }

    @Override
    public String toString() {
        return "Reaction{" +
                "consequences=" + consequences +
                '}';
    }
}
