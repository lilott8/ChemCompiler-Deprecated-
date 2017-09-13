package shared;

import java.util.HashSet;
import java.util.Set;

import chemaxon.struc.Molecule;

/**
 * Programmatic representation of a compound.  Contains a set of reactive groups,
 * a name and a ChemAxon molecule object.  The name is usually just a "SMILES"
 * representation of the molecule -- it acts as a cache as getting the "SMILES"
 * from the ChemAxon molecule is slow
 */
public class Compound {

    private long id = -1;
    private Set<Integer> reactiveGroups = new HashSet<Integer>();
    private String name;
    private Molecule molecule;

    public Compound(long id) {
        this.id = id;
    }

    public Compound(long id, String name) {
        this.id = id;
        this.name = name;
    }

    public Compound(long id, String name, Set<Integer> reactiveGroups) {
        this.id = id;
        this.name = name;
        this.reactiveGroups = reactiveGroups;
    }

    /**
     * Add a reactive group to the set of reactive groups
     *
     * @param group
     */
    public void addReactiveGroup(int group) {
        this.reactiveGroups.add(group);
    }

    /**
     * Add a set of reactive groups to the current set
     * @param groups
     */
    public void addReactiveGroup(Set<Integer> groups) {
        this.reactiveGroups.addAll(groups);
    }

    /**
     * Gets the ID of the compound
     * @return the pubchem id
     */
    public long getId() {
        return id;
    }

    /**
     * Returns the reactive groups the compound belongs to
     * @return set of ints that represent reactive groups
     */
    public Set<Integer> getReactiveGroups() {
        return reactiveGroups;
    }

    /**
     * Returns the name of the compound
     * @return string name
     */
    public String getName() {
        return name;
    }

    /**
     * Returns the ChemAxon molecule object
     * @return molecule object
     */
    public Molecule getMolecule() {
        return molecule;
    }

    /**
     * Set the molecule for the compound
     * @param molecule molecule object
     */
    public void setMolecule(Molecule molecule) {
        this.molecule = molecule;
        //this.molecule.aromatize();
    }

    /**
     * toString method
     * @return string representation of compound
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("ID: ").append(id).append("\t").append("Name: ").append(name);
        sb.append(System.lineSeparator());
        sb.append(reactiveGroups);
        sb.append(System.lineSeparator());
        sb.append(molecule.getName());
        sb.append(System.lineSeparator());
        sb.append(molecule.getAtomCount());
        sb.append(System.lineSeparator());
        sb.append("======");
        sb.append(System.lineSeparator());

        //return sb.toString();
        return name + reactiveGroups;
    }
}

