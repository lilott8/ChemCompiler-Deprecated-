package ir;

import java.util.HashSet;
import java.util.Set;

import chemaxon.jep.function.In;
import chemical.epa.ChemTypes;

/**
 * @created: 2/26/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class TypedInstruction extends Instruction {

    Set<ChemTypes> type = new HashSet<>();

    public TypedInstruction addType(ChemTypes type) {
        this.type.add(type);
        return this;
    }

    public TypedInstruction addTypes(Set<ChemTypes> types) {
        this.type.addAll(types);
        return this;
    }

    public Set<ChemTypes> getTypes() {
        return this.type;
    }
}
