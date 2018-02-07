package symboltable;

import typesystem.epa.ChemTypes;

/**
 * @created: 2/5/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Type {

    private ChemTypes type;

    public Type(ChemTypes type) {
        this.type = type;
    }

    public ChemTypes getType() {
        return this.type;
    }
}
