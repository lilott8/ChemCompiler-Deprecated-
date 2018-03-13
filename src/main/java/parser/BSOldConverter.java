package parser;

import parser.ast.Module;
import shared.Step;

/**
 * @created: 3/13/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSOldConverter extends BSVisitor {
    @Override
    public Step run() {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(Module n) {
        return super.visit(n);
    }
}
