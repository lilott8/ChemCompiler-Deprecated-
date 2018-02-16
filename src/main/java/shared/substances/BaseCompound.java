package shared.substances;

import java.util.HashSet;
import java.util.Set;

import chemaxon.struc.Molecule;
import chemical.epa.ChemTypes;

/**
 * Programmatic representation of a compound.  Contains a set of reactive groups,
 * a name and a ChemAxon molecule object.  The name is usually just a "SMILES"
 * representation of the molecule -- it acts as a cache as getting the "SMILES"
 * from the ChemAxon molecule is slow
 */
public abstract class BaseCompound<T> {

    protected long id = -1;
    protected Set<ChemTypes> reactiveGroups = new HashSet<>();
    protected String name = "unknown";
    protected String smiles = "";

    public BaseCompound(long id) {
        this.id = id;
    }

    public BaseCompound(long id, String name) {
        this.id = id;
        this.name = name;
    }

    public BaseCompound(long id, String name, Set<ChemTypes> reactiveGroups) {
        this.id = id;
        this.name = name;
        this.reactiveGroups = reactiveGroups;
    }

    public abstract T getRepresentation();
    public abstract void setRepresentation(T representation);

    /**
     * Add a reactive group to the set of reactive groups
     *
     * @param group
     */
    public void addReactiveGroup(int group) {
        this.reactiveGroups.add(ChemTypes.getTypeFromId(group));
    }

    public void addReactiveGroup(ChemTypes type) {
        this.reactiveGroups.add(type);
    }

    /**
     * Add a set of reactive groups to the current set
     * @param groups
     */
    public void addReactiveGroup(Set<ChemTypes> groups) {
        this.reactiveGroups.addAll(groups);
    }

    /**
     * Gets the getId of the compound
     * @return the pubchem id
     */
    public long getId() {
        return id;
    }

    /**
     * Returns the reactive groups the compound belongs to
     * @return set of ints that represent reactive groups
     */
    public Set<ChemTypes> getReactiveGroups() {
        return reactiveGroups;
    }

    /**
     * Returns the name of the compound
     * @return string name
     */
    public String getName() {
        return name;
    }

    public void setSmiles(String smiles) {
        this.smiles = smiles;
    }

    public String getSmiles() {
        return this.smiles;
    }
    /**
     * toString method
     * @return string representation of compound
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("getId: ").append(id).append("\t").append("Name: ").append(name);
        sb.append(System.lineSeparator());
        sb.append(reactiveGroups);
        sb.append(System.lineSeparator());

        //return sb.toString();
        return name + reactiveGroups;
    }

    public String getKey() {
        return String.format("%d-%s", 6, "");
    }
}

