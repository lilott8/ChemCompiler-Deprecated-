package simulator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import phases.inference.ChemTypes;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TinyIdentifier implements Identify {

    public static Map<String, Set<ChemTypes>> tinyReactiveGroups = new HashMap<>();
    public static Map<ChemTypes, Set<ChemTypes>> illegalCombos = new HashMap<>();

    static {
        // X
        tinyReactiveGroups.put("blood_2", new HashSet<>());
        // Y
        tinyReactiveGroups.put("water_2", new HashSet<>());
        // Z
        tinyReactiveGroups.put("urine_2", new HashSet<>());
        // mix x,y
        tinyReactiveGroups.put("one_2", new HashSet<>());
        // mix y, z
        tinyReactiveGroups.put("two_2", new HashSet<>());
        // mix one, two
        tinyReactiveGroups.put("three_2", new HashSet<>());

        tinyReactiveGroups.get("aaa_1").add(ChemTypes.A);
        tinyReactiveGroups.get("bbb_1").add(ChemTypes.B);
        tinyReactiveGroups.get("ccc_1").add(ChemTypes.C);

        illegalCombos.put(ChemTypes.A, new HashSet<>());
        illegalCombos.put(ChemTypes.B, new HashSet<>());
        illegalCombos.get(ChemTypes.A).add(ChemTypes.B);
        illegalCombos.get(ChemTypes.B).add(ChemTypes.A);
    }


    @Override
    public Set<ChemTypes> getReactiveGroup(String name) {
        return tinyReactiveGroups.get(name);
    }

    @Override
    public Set<ChemTypes> getReaction(int rg1, int rg2) {
        return null;
    }

    @Override
    public Set<ChemTypes> getReaction(ChemTypes rg1, ChemTypes rg2) {
        Set<ChemTypes> types = new HashSet<>();
        types.add(rg1);
        types.add(rg2);
        return types;
    }
}
