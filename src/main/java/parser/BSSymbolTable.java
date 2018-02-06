package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import sun.awt.Symbol;

import parser.ast.BSProgram;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;

/**
 * @created: 2/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSSymbolTable extends GJNoArguDepthFirst<SymbolTable> implements Step, SymbolTable {

    public static final Logger logger = LogManager.getLogger(BSSymbolTable.class);

    public BSSymbolTable() {

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
