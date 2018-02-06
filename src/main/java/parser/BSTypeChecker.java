package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import parser.ast.BSProgram;
import parser.ast.Node;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;

/**
 * @created: 11/30/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends GJNoArguDepthFirst<Node> implements Step, TypeChecker {

    public static final Logger logger = LogManager.getLogger(BSTypeChecker.class);

    public BSTypeChecker() {
        logger.warn("Not currently type checking anything.");
    }

    @Override
    public String getName() {
        return "BSTypeChecker";
    }

    @Override
    public Step run() {
        return this;
    }
}
