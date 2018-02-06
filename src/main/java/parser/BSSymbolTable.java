package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import parser.ast.BSProgram;
import shared.Step;

/**
 * @created: 2/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSSymbolTable extends SymbolTable implements Step {

    public static final Logger logger = LogManager.getLogger(BSSymbolTable.class);

    private BSProgram program;

    public BSSymbolTable(BSProgram program) {

    }

    @Override
    public Step run() {
        return null;
    }

    @Override
    public String getName() {
        return "BSSymbolTable";
    }
}
