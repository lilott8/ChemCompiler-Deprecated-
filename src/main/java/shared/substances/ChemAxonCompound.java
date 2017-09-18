package shared.substances;

import java.util.Set;

import chemaxon.struc.Molecule;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemAxonCompound extends BaseCompound<Molecule> {

    private Molecule molecule = null;

    public ChemAxonCompound(long id) {
        super(id);
    }

    public ChemAxonCompound(long id, String name) {
        super(id, name);
    }

    public ChemAxonCompound(long id, String name, Set<ChemTypes> reactiveGroups) {
        super(id, name, reactiveGroups);
    }

    /**
     * Returns the ChemAxon molecule object
     * @return molecule object
     */
    @Override
    public Molecule getRepresentation() {
        return this.molecule;
    }

    @Override
    public void setRepresentation(Molecule representation) {
        this.molecule = representation;
    }

    /**
     * Set the molecule for the compound
     * @param molecule molecule object
     */
    public void setMolecule(Molecule molecule) {
        this.molecule = molecule;
    }

    @Override
    protected void setSmiles(String smiles) {
        this.smiles = smiles;

    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(super.toString());
        sb.append(molecule.getName());
        sb.append(System.lineSeparator());
        sb.append(molecule.getAtomCount());
        sb.append(System.lineSeparator());

        return sb.toString();
    }
}
