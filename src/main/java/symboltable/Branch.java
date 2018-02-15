package symboltable;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Branch extends Symbol {

    public Branch(String name, Set<ChemTypes> type) {
        super(name, type);
    }
}
