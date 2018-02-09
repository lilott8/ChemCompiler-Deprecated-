package symboltable;

import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 2/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Loop extends Symbol {

    public Loop(String name, Set<ChemTypes> type) {
        super(name, type);
    }
}
