package shared.substances;

import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveCompound extends BaseCompound<String> {

    public NaiveCompound(long id) {
        super(id);
    }

    public NaiveCompound(long id, String name) {
        super(id, name);
    }

    public NaiveCompound(long id, String name, Set<ChemTypes> reactiveGroups) {
        super(id, name, reactiveGroups);
    }

    @Override
    public String getRepresentation() {
        return null;
    }

    @Override
    public void setRepresentation(String representation) {

    }
}
