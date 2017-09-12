package simulator;

import java.util.Set;

import compilation.datastructures.cfg.CFG;
import phases.inference.ChemTypes;

/**
 * @created: 9/6/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Identify {

    Set<ChemTypes> getReactiveGroup(String name);
    Set<ChemTypes> getReaction(int rg1, int rg2);
    Set<ChemTypes> getReaction(ChemTypes rg1, ChemTypes rg2);

}
