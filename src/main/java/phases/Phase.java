package phases;

import compilation.datastructures.cfg.CFG;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Phase {

    boolean runPhase(CFG controlFlowGraph);
}
