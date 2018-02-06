package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import parser.ast.BSProgram;
import shared.Step;

/**
 * @created: 11/30/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends TypeChecker implements Step {

    public static final Logger logger = LogManager.getLogger(BSTypeChecker.class);
    private BSProgram program;

    public BSTypeChecker(BSProgram program) {
        this.program = program;
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
