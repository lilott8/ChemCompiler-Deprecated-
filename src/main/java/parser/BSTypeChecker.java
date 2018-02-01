package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import parser.ast.BSProgram;
import shared.Step;

/**
 * @created: 11/30/17
 * @since: 0.1
 * @project: MiniComplier
 */
public class BSTypeChecker implements Step {

    public static final Logger logger = LogManager.getLogger(BSTypeChecker.class);
    BSProgram program;

    public BSTypeChecker(BSProgram program) {
        this.program = program;
    }

    @Override
    public String getName() {
        return "BioScript Type Checker Strategy";
    }

    @Override
    public Step run() {
        this.buildSymbolTable();
        this.runTypecheck();
        return this;
    }


    private void buildSymbolTable() {

    }

    private void runTypecheck() {
        logger.info("We are assuming all MJ programs are correctly typed right now.");
    }
}
